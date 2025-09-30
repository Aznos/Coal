package codegen

import ast.*
import codegen.ir.BlockBuilder
import codegen.ir.ModuleBuilder
import diagnostics.CoalError
import diagnostics.Diagnostic
import diagnostics.ErrorCode
import diagnostics.Severity
import diagnostics.Span
import front.types.TypeInfo

/**
 * The main class used for emitting LLVM IR from the AST
 *
 * @param types The type information from the frontend
 * @param fileName The source file name (for error reporting)
 */
class LLVMEmitter(
    private val types: TypeInfo,
    private val fileName: String = "<codegen>"
) {
    /**
     * An RValue represents a value computed from an expression
     * - Immediate: A constant value (e.g., integer literal)
     * - ValueReg: A value stored in a register
     * - Aggregate: A composite value (e.g., string struct)
     */
    private sealed interface RValue {
        data class Immediate(val llTy: String, val text: String) : RValue
        data class ValueReg(val llTy: String, val reg: String) : RValue
        data class Aggregate(val literal: String) : RValue
    }

    /**
     * A LocalSlot represents a local variable's storage in LLVM IR
     *
     * @param llTy The LLVM type of the variable
     * @param reg The register (pointer) where the variable is stored
     */
    private data class LocalSlot(val llTy: String, val reg: String)

    private lateinit var mod: ModuleBuilder
    private val locals = LinkedHashMap<String, LocalSlot>()
    private val dbgGlobals = mutableListOf<String>()
    private var currentFn = ""

    private var labelCounter = 0

    /**
     * Emit LLVM IR for the given program
     *
     * @param prog The AST of the program to compile
     * @return The generated LLVM IR as a string
     */
    fun emit(prog: Program): String {
        mod = ModuleBuilder()

        mod.declarePrintf()
        mod.declareSnprintf()
        mod.declareStrlen()
        mod.declareMalloc()
        mod.declareMemcpy()
        mod.declareStrtol()
        mod.declareStrtod()
        mod.declareGetchar()

        for(d in prog.decls) {
            when(d) {
                is FnDecl -> emitFn(d)
            }
        }

        return mod.toString()
    }

    private fun emitFn(fn: FnDecl) {
        currentFn = fn.name
        locals.clear()

        val fb = mod.function(fn.name, retTy = "i32").start()
        val b = fb.block("entry")

        for(s in fn.body.stmts) {
            when(s) {
                is VarDecl -> lowerVarDecl(b, fn.name, s)
                is Assign -> lowerAssign(b, fn.name, s)
                is ExprStmt -> valueOfExpr(b, s.expr)
                is IfStmt -> lowerIf(b, s)
                is WhileStmt -> lowerWhile(b, s)
            }
        }

        b.ret("i32", "0")
        fb.end()
    }

    private fun lowerVarDecl(b: BlockBuilder, fnName: String, decl: VarDecl) {
        val ty = types.typeOfVar(fnName, decl.name)
        val llTy = llTypeOf(ty)
        val slotPtr = b.alloca(llTy, decl.name)

        if(decl.init != null) {
            val rhs = valueOfExpr(b, decl.init, llTy)
            when(rhs) {
                is RValue.Immediate -> b.store(rhs.llTy, rhs.text, slotPtr)
                is RValue.ValueReg -> b.store(rhs.llTy, rhs.reg, slotPtr)
                is RValue.Aggregate -> b.store(llTy, rhs.literal, slotPtr)
            }
        } else {
            b.store(llTy, zeroInit(llTy), slotPtr)
        }

        locals[decl.name] = LocalSlot(llTy, slotPtr)
        val t = b.load(llTy, slotPtr)
        val dbgName = "__dbg_${fnName}_${decl.name}"

        ensureDbgGlobal(dbgName, llTy)
        b.store(llTy, t, "@$dbgName")
    }

    private fun lowerAssign(b: BlockBuilder, fnName: String, asg: Assign) {
        val slot = locals[asg.name] ?: ice("Local not found for ${asg.name}", asg.span)
        val rhs = valueOfExpr(b, asg.value, slot.llTy)
        when(rhs) {
            is RValue.Immediate -> b.store(rhs.llTy, rhs.text, slot.reg)
            is RValue.ValueReg -> b.store(rhs.llTy, rhs.reg, slot.reg)
            is RValue.Aggregate -> b.store(slot.llTy, rhs.literal, slot.reg)
        }

        val t = b.load(slot.llTy, slot.reg)
        val dbgName = "__dbg_${fnName}_${asg.name}"
        ensureDbgGlobal(dbgName, slot.llTy)
        b.store(slot.llTy, t, "@$dbgName")
    }

    private fun lowerIf(b: BlockBuilder, s: IfStmt) {
        val end = fresh("if_end")
        val thenLabels = s.branches.indices.map { fresh("if_then$it") }
        val checkLabels = s.branches.indices.drop(1).map { fresh("if_chk$it") }
        val elseLabel = s.elseBranch?.let { fresh("if_else") }

        fun condTo(bld: BlockBuilder, cond: Expr, thenLabel: String, elseLabel: String) {
            val rv = valueOfExpr(bld, cond)
            val (ty, op) = asOperand(rv)
            if(ty != "i1") ice("if condition must be a boolean, got $ty", cond.span)
            bld.brCond("i1", op, thenLabel, elseLabel)
        }

        val nextAfterFirst = checkLabels.firstOrNull() ?: elseLabel ?: end
        condTo(b, s.branches.first().condition, thenLabels.first(), nextAfterFirst)

        s.branches.drop(1).forEachIndexed { idx, br ->
            val cb = b.nextBlock(checkLabels[idx])
            val elseTgt = if(idx == s.branches.size - 2) (elseLabel ?: end) else checkLabels[idx + 1]
            condTo(cb, br.condition, thenLabels[idx + 1], elseTgt)
        }

        s.branches.forEachIndexed { i, br ->
            val tb = b.nextBlock(thenLabels[i])
            br.body.stmts.forEach { st ->
                when(st) {
                    is VarDecl -> lowerVarDecl(tb, currentFn, st)
                    is Assign -> lowerAssign(tb, currentFn, st)
                    is ExprStmt -> valueOfExpr(tb, st.expr)
                    is IfStmt -> lowerIf(tb, st)
                    is WhileStmt -> lowerWhile(tb, st)
                }
            }

            tb.br(end)
        }

        if(s.elseBranch != null) {
            val eb = b.nextBlock(elseLabel!!)
            s.elseBranch.stmts.forEach { st ->
                when(st) {
                    is VarDecl -> lowerVarDecl(eb, currentFn, st)
                    is Assign -> lowerAssign(eb, currentFn, st)
                    is ExprStmt -> valueOfExpr(eb, st.expr)
                    is IfStmt -> lowerIf(eb, st)
                    is WhileStmt -> lowerWhile(eb, st)
                }
            }

            eb.br(end)
        }

        b.nextBlock(end)
    }

    private fun lowerWhile(b: BlockBuilder, s: WhileStmt) {
        val end = fresh("while_end")
        val body = fresh("while_body")

        fun condTo(thenLabel: String, elseLabel: String) {
            val rv = valueOfExpr(b, s.condition)
            val (ty, op) = asOperand(rv)
            if(ty != "i1") ice("while condition must be a boolean, got $ty", s.condition.span)
            b.brCond("i1", op, thenLabel, elseLabel)
        }

        condTo(body, end)

        val tb = b.nextBlock(body)
        s.body.stmts.forEach { st ->
            when(st) {
                is VarDecl -> lowerVarDecl(tb, currentFn, st)
                is Assign -> lowerAssign(tb, currentFn, st)
                is ExprStmt -> valueOfExpr(tb, st.expr)
                is IfStmt -> lowerIf(tb, st)
                is WhileStmt -> lowerWhile(tb, st)
            }
        }

        condTo(body, end)

        tb.br(end)
        b.nextBlock(end)
    }

    private fun valueOfExpr(b: BlockBuilder, e: Expr, expected: String? = null): RValue = when(e) {
        is IntLit -> RValue.Immediate("i32", e.value.toString())
        is FloatLit -> RValue.Immediate("double", e.value.toString())
        is BoolLit -> RValue.Immediate("i1", if(e.value) "1" else "0")
        is CharLit -> RValue.Immediate("i8", e.value.toString())
        is StringLit -> {
            val ref = mod.internCString(e.value)
            val len = utf8Len(e.value)
            RValue.Aggregate("{ ptr ${ref.constGEP}, i32 $len }")
        }

        is Ident -> {
            val slot = locals[e.name] ?: ice("Local not found for ${e.name}", e.span)
            val t = b.load(slot.llTy, slot.reg)
            RValue.ValueReg(slot.llTy, t)
        }

        is Binary -> lowerBinary(b, e)
        is Call -> when(e.callee) {
            "print" -> lowerBuiltinPrint(b, e.args, false)
            "println" -> lowerBuiltinPrint(b, e.args, true)
            "input" -> lowerBuiltinInput(b, e.args)
            else -> ice("unknown function call: ${e.callee}", e.span)
        }

        is Unary -> when(e.op) {
            UnOp.Not -> {
                val v = valueOfExpr(b, e.expr)
                val (ty, op) = asOperand(v)
                if(ty != "i1") ice("! operator requires boolean operand, got $ty", e.span)
                val t = b.xorI1(op)
                RValue.ValueReg("i1", t)
            }
        }

        is MethodCall -> lowerMethodCall(b, e)
    }

    private fun lowerBinary(b: BlockBuilder, bin: Binary): RValue {
        when(bin.op) {
            BinOp.And -> {
                val lhs = valueOfExpr(b, bin.left)
                val (lty, lop) = asOperand(lhs)
                if(lty != "i1") ice("left operand of && must be boolean, got $lty", bin.left.span)

                val evalR = fresh("and_r")
                val falseBlk = fresh("and_false")
                val done = fresh("and_end")

                b.brCond("i1", lop, evalR, falseBlk)
                val tb = b.nextBlock(evalR)
                val rhs = valueOfExpr(tb, bin.right)
                val (rty, rop) = asOperand(rhs)
                if(rty != "i1") ice("right operand of && must be boolean, got $rty", bin.right.span)
                tb.br(done)

                val fb = b.nextBlock(falseBlk)
                fb.br(done)

                val jb = b.nextBlock(done)
                val phi = jb.phi("i1", "0" to falseBlk, rop to evalR)
                return RValue.ValueReg("i1", phi)
            }

            BinOp.Or -> {
                val lhs = valueOfExpr(b, bin.left)
                val (lty, lop) = asOperand(lhs)
                if(lty != "i1") ice("left operand of || must be boolean, got $lty", bin.left.span)

                val trueBlk = fresh("or_true")
                val evalR = fresh("or_r")
                val done = fresh("or_end")

                b.brCond("i1", lop, trueBlk, evalR)
                val tb = b.nextBlock(trueBlk)
                tb.br(done)

                val rb = b.nextBlock(evalR)
                val rhs = valueOfExpr(rb, bin.right)
                val (rty, rop) = asOperand(rhs)
                if(rty != "i1") ice("right operand of || must be boolean, got $rty", bin.right.span)
                rb.br(done)

                val jb = b.nextBlock(done)
                val phi = jb.phi("i1", "1" to trueBlk, rop to evalR)
                return RValue.ValueReg("i1", phi)
            }

            else -> {}
        }

        when(bin.op) {
            BinOp.Eq, BinOp.Ne, BinOp.Lt, BinOp.Le, BinOp.Gt, BinOp.Ge -> {
                val lrv = valueOfExpr(b, bin.left)
                val rrv = valueOfExpr(b, bin.right)

                val (lt, lo) = asOperand(lrv)
                val (rt, ro) = asOperand(rrv)
                if (lt != rt) ice("cmp operands mismatch: $lt vs $rt", bin.span)

                val out = when(lt) {
                    "i32", "i8", "i1" -> {
                        val pred = when(bin.op) {
                            BinOp.Eq -> "eq"; BinOp.Ne -> "ne"
                            BinOp.Lt -> "slt"; BinOp.Le -> "sle"
                            BinOp.Gt -> "sgt"; BinOp.Ge -> "sge"
                            else -> ice("bad int cmp", bin.span)
                        }
                        b.icmp(pred, lt, lo, ro)
                    }

                    "double" -> {
                        val pred = when(bin.op) {
                            BinOp.Eq -> "oeq"; BinOp.Ne -> "one"
                            BinOp.Lt -> "olt"; BinOp.Le -> "ole"
                            BinOp.Gt -> "ogt"; BinOp.Ge -> "oge"
                            else -> ice("bad fp cmp", bin.span)
                        }
                        b.fcmp(pred, lo, ro)
                    }

                    "{ ptr, i32 }" -> {
                        val lp = extractStringPtr(b, lrv)
                        val rp = extractStringPtr(b, rrv)
                        val pred = if(bin.op == BinOp.Eq) "eq" else "ne"
                        b.icmp(pred, "ptr", lp, rp)
                    }

                    else -> ice("cmp unsupported llty $lt", bin.span)
                }

                return RValue.ValueReg("i1", out)
            }

            else -> {}
        }

        run {
            val ty = types.typeOf(bin)
            if(ty.name == "string") {
                val lhs = valueOfExpr(b, bin.left)
                val rhs = valueOfExpr(b, bin.right)
                return concatStrings(b, lhs, rhs)
            }
        }

        val resTy = types.typeOf(bin)
        val llTy = when(resTy.name) {
            "float" -> "double"
            "int"   -> "i32"
            "char"  -> "i8"
            else    -> ice("unsupported type ${resTy.name} in arithmetic", bin.span)
        }

        fun asOp(rv: RValue): String = when(rv) {
            is RValue.Immediate -> rv.text
            is RValue.ValueReg  -> rv.reg
            is RValue.Aggregate -> ice("aggregate used as scalar op", bin.span)
        }

        var lhs = valueOfExpr(b, bin.left)
        var rhs = valueOfExpr(b, bin.right)

        fun maybeZextToI32(v: RValue): RValue = when (v) {
            is RValue.ValueReg -> if (v.llTy == "i8") {
                val z = b.zext("i8", v.reg, "i32")
                RValue.ValueReg("i32", z)
            } else v

            is RValue.Immediate -> if(v.llTy == "i8") RValue.Immediate("i32", v.text) else v
            else -> v
        }

        val useFloat = (llTy == "double")
        if(!useFloat) {
            lhs = maybeZextToI32(lhs)
            rhs = maybeZextToI32(rhs)
        }

        val a = asOp(lhs)
        val c = asOp(rhs)
        val reg = when(bin.op) {
            BinOp.Pow -> if(useFloat) b.fpow(a, c) else b.pow(a, c)
            BinOp.Add -> if(useFloat) b.fadd(a, c) else b.add("i32", a, c)
            BinOp.Sub -> if(useFloat) b.fsub(a, c) else b.sub("i32", a, c)
            BinOp.Mul -> if(useFloat) b.fmul(a, c) else b.mul("i32", a, c)
            BinOp.Div -> if(useFloat) b.fdiv(a, c) else b.sdiv("i32", a, c)
            BinOp.Mod -> { if(useFloat) ice("mod on float", bin.span); b.srem("i32", a, c) }
            else -> ice("unexpected binop ${bin.op} in arithmetic", bin.span)
        }

        return RValue.ValueReg(if (useFloat) "double" else "i32", reg)
    }

    private fun lowerMethodCall(b: BlockBuilder, m: MethodCall): RValue {
        val recv = valueOfExpr(b, m.receiver)

        fun isStringLike(v: RValue) = (v is RValue.ValueReg && v.llTy == "{ ptr, i32 }") || (v is RValue.Aggregate)
        fun stringPtrOf(v: RValue): String = when(v) {
            is RValue.Aggregate -> b.extractValue("{ ptr, i32 }", v.literal, 0)
            is RValue.ValueReg  -> b.extractValue("{ ptr, i32 }", v.reg, 0)
            else -> ice("Expected string aggregate")
        }

        fun stringLenOf(v: RValue): String = when(v) {
            is RValue.Aggregate -> b.extractValue("{ ptr, i32 }", v.literal, 1)
            is RValue.ValueReg  -> b.extractValue("{ ptr, i32 }", v.reg, 1)
            else -> ice("Expected string aggregate")
        }

        return when (m.method) {
            "toString" -> when (recv) {
                is RValue.Aggregate -> recv // already string
                is RValue.Immediate, is RValue.ValueReg -> numberOrCharToString(b, recv)
            }

            "toInt" -> when {
                (recv is RValue.Immediate && recv.llTy == "double") || (recv is RValue.ValueReg  && recv.llTy == "double") -> {
                    val i = b.fptosi("double", asOperand(recv).second, "i32")
                    RValue.ValueReg("i32", i)
                }

                (recv is RValue.Immediate && recv.llTy == "i8") || (recv is RValue.ValueReg  && recv.llTy == "i8") -> {
                    val z = when(recv) {
                        is RValue.Immediate -> recv.text
                        is RValue.ValueReg -> {
                            val t = b.zext("i8", recv.reg, "i32"); t
                        }

                        else -> ice("unreachable toInt char")
                    }

                    if(recv is RValue.Immediate) RValue.Immediate("i32", z) else RValue.ValueReg("i32", z)
                }

                (recv is RValue.Immediate && recv.llTy == "i1") || (recv is RValue.ValueReg  && recv.llTy == "i1") -> {
                    val z = when(recv) {
                        is RValue.Immediate -> recv.text
                        is RValue.ValueReg  -> b.zext("i1", recv.reg, "i32")
                        else -> ice("unreachable toInt bool")
                    }

                    if(recv is RValue.Immediate) RValue.Immediate("i32", z) else RValue.ValueReg("i32", z)
                }

                m.receiver is StringLit -> stringToIntIfLiteral(m.receiver)
                isStringLike(recv) -> {
                    val nptr = stringPtrOf(recv)
                    val r64 = b.call("strtol", "i64", "ptr" to nptr, "ptr" to "null", "i32" to "10")
                    val r32 = b.trunc("i64", r64, "i32")
                    RValue.ValueReg("i32", r32)
                }

                (recv is RValue.Immediate && recv.llTy == "i32") || (recv is RValue.ValueReg  && recv.llTy == "i32") -> recv
                else -> ice("toInt() recv type unsupported", m.span)
            }

            "toFloat" -> when {
                (recv is RValue.Immediate && recv.llTy in listOf("i32","i8","i1")) || (recv is RValue.ValueReg  && recv.llTy in listOf("i32","i8","i1")) -> {
                    val asI32 = when(recv) {
                        is RValue.Immediate -> when(recv.llTy) {
                            "i32" -> recv.text
                            "i8","i1" -> recv.text
                            else -> ice("bad toFloat immediate")
                        }

                        is RValue.ValueReg -> when(recv.llTy) {
                            "i32" -> recv.reg
                            "i8"  -> b.zext("i8", recv.reg, "i32")
                            "i1"  -> b.zext("i1", recv.reg, "i32")
                            else -> ice("bad toFloat reg")
                        }

                        else -> ice("unreachable toFloat intlike")
                    }

                    val f = b.sitofp("i32", asI32, "double")
                    RValue.ValueReg("double", f)
                }

                m.receiver is StringLit -> stringToFloatIfLiteral(m.receiver)
                isStringLike(recv) -> {
                    val nptr = stringPtrOf(recv)
                    val f = b.call("strtod", "double", "ptr" to nptr, "ptr" to "null")
                    RValue.ValueReg("double", f)
                }

                (recv is RValue.Immediate && recv.llTy == "double") || (recv is RValue.ValueReg  && recv.llTy == "double") -> recv
                else -> ice("toFloat() recv type unsupported", m.span)
            }

            "toBool" -> when {
                (recv is RValue.Immediate && recv.llTy in listOf("i32","i8")) || (recv is RValue.ValueReg  && recv.llTy in listOf("i32","i8")) -> {
                    val asI32 = when(recv) {
                        is RValue.Immediate -> if(recv.llTy=="i32") recv.text else recv.text
                        is RValue.ValueReg  -> if(recv.llTy=="i32") recv.reg else b.zext("i8", recv.reg, "i32")
                        else -> ice("unreachable toBool int/char")
                    }

                    val nz = b.icmp("ne", "i32", asI32, "0")
                    RValue.ValueReg("i1", nz)
                }

                (recv is RValue.Immediate && recv.llTy == "double") || (recv is RValue.ValueReg  && recv.llTy == "double") -> {
                    val nz = b.fcmp("one", asOperand(recv).second, "0.0")
                    RValue.ValueReg("i1", nz)
                }

                isStringLike(recv) -> {
                    val len = stringLenOf(recv)
                    val pos = b.icmp("sgt", "i32", len, "0")
                    RValue.ValueReg("i1", pos)
                }

                (recv is RValue.Immediate && recv.llTy == "i1") || (recv is RValue.ValueReg  && recv.llTy == "i1") -> recv
                else -> ice("toBool() recv type unsupported", m.span)
            }

            "toChar" -> when {
                (recv is RValue.Immediate && recv.llTy == "i32") -> {
                    val v8 = (asOperand(recv).second.toInt() and 0xFF).toString()
                    RValue.Immediate("i8", v8)
                }

                (recv is RValue.ValueReg && recv.llTy == "i32") -> {
                    val t = b.trunc("i32", recv.reg, "i8")
                    RValue.ValueReg("i8", t)
                }

                (recv is RValue.ValueReg && recv.llTy == "i1") -> {
                    val z = b.zext("i1", recv.reg, "i8")
                    RValue.ValueReg("i8", z)
                }

                (recv is RValue.Immediate && recv.llTy == "i1") -> RValue.Immediate("i8", recv.text)
                (recv is RValue.ValueReg && recv.llTy == "double") -> {
                    val i = b.fptosi("double", recv.reg, "i32")
                    val t = b.trunc("i32", i, "i8")
                    RValue.ValueReg("i8", t)
                }

                (recv is RValue.Immediate && recv.llTy == "double") -> {
                    val i = b.fptosi("double", recv.text, "i32")
                    val t = b.trunc("i32", i, "i8")
                    RValue.ValueReg("i8", t)
                }

                isStringLike(recv) -> {
                    val p = stringPtrOf(recv)
                    val len = stringLenOf(recv)
                    val isEmpty = b.icmp("eq", "i32", len, "0")
                    val L_take = fresh("tochar_take")
                    val L_zero = fresh("tochar_zero")
                    val L_join = fresh("tochar_join")
                    b.brCond("i1", isEmpty, L_zero, L_take)
                    val bt = b.nextBlock(L_take)
                    val c32 = bt.zext("i8", bt.load("i8", p), "i32")
                    bt.br(L_join)
                    val bz = b.nextBlock(L_zero)
                    bz.br(L_join)
                    val bj = b.nextBlock(L_join)
                    val cSel = bj.phi("i32", "0" to L_zero, c32 to L_take)
                    val c8 = bj.trunc("i32", cSel, "i8")
                    RValue.ValueReg("i8", c8)
                }

                (recv is RValue.Immediate && recv.llTy == "i8") || (recv is RValue.ValueReg  && recv.llTy == "i8") -> recv
                else -> ice("toChar() recv type unsupported", m.span)
            }

            else -> ice("Unknown method: ${m.method}", m.span)
        }
    }

    private fun lowerBuiltinPrint(b: BlockBuilder, args: List<Expr>, newline: Boolean): RValue {
        if(args.size != 1) ice("print/println expects 1 argument, got ${args.size}", args.firstOrNull()?.span ?: Span(0,0,1,1))
        val rv = valueOfExpr(b, args[0])

        fun isStringAggReg(v: RValue) = v is RValue.ValueReg && v.llTy == "{ ptr, i32 }"
        if(rv is RValue.Aggregate || isStringAggReg(rv)) {
            val fmtRef = mod.internCString(if(newline) "%s\n" else "%s")
            val fmtPtr = b.gepGlobalFirst(fmtRef)
            val strPtr = when(rv) {
                is RValue.Aggregate -> b.extractValue("{ ptr, i32 }", rv.literal, 0)
                is RValue.ValueReg  -> b.extractValue("{ ptr, i32 }", rv.reg, 0)
                else -> ice("Unreachable print string", args[0].span)
            }

            b.callPrintf(fmtPtr, "ptr" to strPtr)
            return RValue.Immediate("i32", "0")
        }

        val (ty, op) = asOperand(rv)
        val fmt = when(ty) {
            "i32", "i1", "i8" -> if(newline) "%d\n" else "%d"
            "double"          -> if(newline) "%f\n" else "%f"
            else              -> ice("Print unsupported llty $ty", args[0].span)
        }

        val fmtG = mod.internCString(fmt)
        val argTy = if (ty == "i1" || ty == "i8") "i32" else ty
        b.callPrintf(fmtG.constGEP, argTy to op)
        return RValue.Immediate("i32", "0")
    }

    private fun lowerBuiltinInput(b: BlockBuilder, args: List<Expr>): RValue {
        if(args.size != 1) ice("input() expects 1 argument, got ${args.size}", args.firstOrNull()?.span ?: Span(0,0,1,1))

        val prompt = valueOfExpr(b, args[0])
        val promptPtr = when(prompt) {
            is RValue.Aggregate -> b.extractValue("{ ptr, i32 }", prompt.literal, 0)
            is RValue.ValueReg  -> b.extractValue("{ ptr, i32 }", prompt.reg, 0)
            else -> ice("input(prompt): prompt must be string", args[0].span)
        }

        val fmtPrompt = mod.internCString("%s")
        b.callPrintf(b.gepGlobalFirst(fmtPrompt), "ptr" to promptPtr)

        val max = 1024
        val buf = b.allocaArray(max, "i8", "inbuf")
        val bufPtr = b.gepFirst(buf, max, "i8")

        val iPtr = b.alloca("i32", "i")
        b.store("i32", "0", iPtr)

        val L_loop     = fresh("in_loop")
        val L_read     = fresh("in_read")
        val L_checkNL  = fresh("in_check_nl")
        val L_store    = fresh("in_store")
        val L_done     = fresh("in_done")
        val L_chkCR    = fresh("in_chkcr")
        val L_afterCR  = fresh("in_aftercr")
        val L_skipCR   = fresh("in_skipcr")

        b.br(L_loop)
        val bl = b.nextBlock(L_loop)
        val iVal = bl.load("i32", iPtr)
        val full = bl.icmp("sge", "i32", iVal, (max - 1).toString())
        bl.brCond("i1", full, L_done, L_read)

        val brd = b.nextBlock(L_read)
        val ch = brd.call("getchar", "i32")
        val isEOF = brd.icmp("eq", "i32", ch, "-1")
        brd.brCond("i1", isEOF, L_done, L_checkNL)

        val bnl = b.nextBlock(L_checkNL)
        val isNL = bnl.icmp("eq", "i32", ch, "10")
        bnl.brCond("i1", isNL, L_done, L_store)

        val bst = b.nextBlock(L_store)
        val iCur = bst.load("i32", iPtr)
        val dstPtr = bst.gepByteOffset(bufPtr, iCur)
        val ch8 = bst.trunc("i32", ch, "i8")
        bst.store("i8", ch8, dstPtr)
        val iNext = bst.add("i32", iCur, "1")
        bst.store("i32", iNext, iPtr)
        bst.br(L_loop)

        val bd = b.nextBlock(L_done)
        val len0 = bd.load("i32", iPtr)

        val hasAny = bd.icmp("sgt", "i32", len0, "0")
        bd.brCond("i1", hasAny, L_chkCR, L_afterCR)

        val bcr = b.nextBlock(L_chkCR)
        val lenm1 = bcr.sub("i32", len0, "1")
        val lastPtr = bcr.gepByteOffset(bufPtr, lenm1)
        val last8 = bcr.load("i8", lastPtr)
        val last32 = bcr.zext("i8", last8, "i32")
        val isCR = bcr.icmp("eq", "i32", last32, "13")
        bcr.brCond("i1", isCR, L_skipCR, L_afterCR)

        val bsk = b.nextBlock(L_skipCR)
        bsk.store("i32", lenm1, iPtr)
        bsk.br(L_afterCR)

        val baf = b.nextBlock(L_afterCR)
        val len = baf.load("i32", iPtr)

        val nulDst = baf.gepByteOffset(bufPtr, len)
        baf.store("i8", "0", nulDst)
        val cap32 = baf.add("i32", len, "1")
        val cap64 = baf.zext("i32", cap32, "i64")
        val dst = baf.call("malloc", "ptr", "i64" to cap64)
        val len64 = baf.zext("i32", len, "i64")
        baf.call("memcpy", "ptr", "ptr" to dst, "ptr" to bufPtr, "i64" to len64)
        val nulH = baf.gepByteOffset(dst, len)
        baf.store("i8", "0", nulH)

        val packed = baf.packString(dst, len)
        return RValue.ValueReg("{ ptr, i32 }", packed)
    }

    private fun llTypeOf(t: NamedType) = when(t.name) {
        "int"    -> "i32"
        "float"  -> "double"
        "bool"   -> "i1"
        "char"   -> "i8"
        "string" -> "{ ptr, i32 }"
        else     -> ice("Unknown frontend type ${t.name}", t.span)
    }

    private fun numberOrCharToString(b: BlockBuilder, rv: RValue): RValue {
        val (ty, op) = asOperand(rv)
        val fmt = when(ty) {
            "i32","i1","i8" -> "%d"
            "double"        -> "%f"
            else            -> ice("toString() unsupported llty $ty")
        }

        val fmtRef = mod.internCString(fmt)
        val fmtPtr = b.gepGlobalFirst(fmtRef)

        val buf = b.allocaArray(64, "i8")
        val bufPtr = b.gepFirst(buf, 64, "i8")

        val wrote = b.callSnprintf(
            bufPtr, 64, fmtPtr,
            if (ty == "i1" || ty == "i8") "i32" to op else ty to op
        )

        val ssa = b.packString(bufPtr, wrote)
        return RValue.ValueReg("{ ptr, i32 }", ssa)
    }

    private fun stringToIntIfLiteral(recv: Expr): RValue =
        when(recv) {
            is StringLit -> {
                val s = recv.value.trim()
                val v = s.toLongOrNull() ?: ice("String literal toInt() failed: '$s'", recv.span)
                RValue.Immediate("i32", v.toString())
            }

            else -> ice("toInt fast-path expects StringLit", recv.span)
        }

    private fun stringToFloatIfLiteral(recv: Expr): RValue =
        when(recv) {
            is StringLit -> {
                val s = recv.value.trim()
                val v = s.toDoubleOrNull() ?: ice("String literal toFloat() failed: '$s'", recv.span)
                RValue.Immediate("double", v.toString())
            }

            else -> ice("toFloat fast-path expects StringLit", recv.span)
        }

    private fun concatStrings(b: BlockBuilder, a: RValue, c: RValue): RValue {
        fun parts(rv: RValue): Pair<String, String> = when(rv) {
            is RValue.Aggregate -> {
                val p = b.extractValue("{ ptr, i32 }", rv.literal, 0)
                val l = b.extractValue("{ ptr, i32 }", rv.literal, 1)
                p to l
            }

            is RValue.ValueReg -> {
                if(rv.llTy != "{ ptr, i32 }") ice("Concat expects string reg, got ${rv.llTy}")
                val p = b.extractValue("{ ptr, i32 }", rv.reg, 0)
                val l = b.extractValue("{ ptr, i32 }", rv.reg, 1)
                p to l
            }

            is RValue.Immediate -> ice("concat immediate (unexpected)")
        }

        val (aPtr, aLen) = parts(a)
        val (cPtr, cLen) = parts(c)
        val totalLen = b.add("i32", aLen, cLen)

        val one = "1"
        val capI32 = b.add("i32", totalLen, one)
        val capI64 = b.zext("i32", capI32, "i64")
        val buf = b.call("malloc", "ptr", "i64" to capI64)

        val aLen64 = b.zext("i32", aLen, "i64")
        b.call("memcpy", "ptr", "ptr" to buf,  "ptr" to aPtr, "i64" to aLen64)

        val dst2 = b.gepByteOffset(buf, aLen)
        val cLen64 = b.zext("i32", cLen, "i64")
        b.call("memcpy", "ptr", "ptr" to dst2, "ptr" to cPtr, "i64" to cLen64)

        val nulPtr = b.gepByteOffset(buf, totalLen)
        b.store("i8", "0", nulPtr)

        val packed = b.packString(buf, totalLen)
        return RValue.ValueReg("{ ptr, i32 }", packed)
    }

    private fun asOperand(rv: RValue): Pair<String, String> = when(rv) {
        is RValue.Immediate -> rv.llTy to rv.text
        is RValue.ValueReg  -> rv.llTy to rv.reg
        is RValue.Aggregate -> ice("Aggregate used as scalar")
    }

    private fun ensureDbgGlobal(name: String, llTy: String) {
        if(name !in dbgGlobals) {
            mod.global(name, llTy, zeroInit(llTy))
            dbgGlobals += name
        }
    }

    private fun zeroInit(ty: String) = when(ty) {
        "i1","i8","i32" -> "0"
        "double"        -> "0.0"
        "{ ptr, i32 }"  -> "{ ptr null, i32 0 }"
        else            -> ice("no zero init for $ty")
    }

    private fun extractStringPtr(b: BlockBuilder, rv: RValue): String = when(rv) {
        is RValue.Aggregate -> b.extractValue("{ ptr, i32 }", rv.literal, 0)
        is RValue.ValueReg  -> b.extractValue("{ ptr, i32 }", rv.reg, 0)
        else -> ice("expected string aggregate")
    }

    private fun utf8Len(s: String) = s.toByteArray(Charsets.UTF_8).size
    private fun fresh(base: String) = "${base}_${labelCounter++}"

    private fun ice(msg: String, span: Span = Span(0,0,1,1)): Nothing {
        throw CoalError(
            Diagnostic(
                Severity.ERROR,
                ErrorCode.Internal,
                fileName,
                span,
                listOf(msg)
            )
        )
    }
}
