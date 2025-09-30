package front.types

import ast.Assign
import ast.BinOp
import ast.Binary
import ast.Block
import ast.BoolLit
import ast.Call
import ast.CharLit
import ast.Expr
import ast.ExprStmt
import ast.FloatLit
import ast.FnDecl
import ast.Ident
import ast.IfStmt
import ast.IntLit
import ast.MethodCall
import ast.NamedType
import ast.Program
import ast.Stmt
import ast.StringLit
import ast.TypeRef
import ast.UnOp
import ast.Unary
import ast.VarDecl
import ast.WhileStmt
import diagnostics.CoalError
import diagnostics.Diagnostic
import diagnostics.ErrorCode
import diagnostics.Severity
import diagnostics.Span
import kotlin.collections.forEach

/**
 * This is the main Type Checker for Coal, once the parser is done with its work, this will be called before the code is given to LLVM.
 * The main purpose of this is to ensure that the program is type-safe and for example strings are not added to integers
 *
 * @param fileName The name of the file being checked, used for error reporting
 * @param sourceText The source text of the file being checked, used for error reporting
 * @param types The TypeInfo object to store type information in
 */
class TypeChecker(
    private val fileName: String,
    private val sourceText: String,
    private val types: TypeInfo
) {
    /**
     * Holds information about a variable in the current scope
     *
     * @param type The type of the variable
     * @param isConst Whether the variable is a constant
     * @param span The span of the variable declaration, used for error reporting
     */
    private data class VarInfo(val type: NamedType, val isConst: Boolean, val span: Span)

    private val env = ArrayDeque<LinkedHashMap<String, VarInfo>>()
    private val functions = linkedMapOf<String, Pair<List<NamedType>, NamedType?>>() // name -> (params, returnType)

    private var currentFn: String = "<global>"

    /**
     * Checks the given program for type errors, populating the TypeInfo object with type information as it goes
     *
     * @param program The program to check
     */
    fun check(program: Program) {
        program.decls.forEach { d ->
            if(d is FnDecl) functions[d.name] = emptyList<NamedType>() to NamedType("int", d.span)
        }

        program.decls.forEach { d ->
            when(d) {
                is FnDecl -> checkFn(d)
            }
        }
    }

    private fun checkFn(fn: FnDecl) {
        currentFn = fn.name
        pushScope()
        checkBlock(fn.body)
        popScope()
        currentFn = "<global>"
    }

    private fun checkBlock(block: Block) {
        pushScope()
        block.stmts.forEach(::checkStmt)
        popScope()
    }

    private fun checkStmt(stmt: Stmt) {
        when(stmt) {
            is VarDecl -> {
                if(current().containsKey(stmt.name)) error(stmt.span, ErrorCode.RedeclaredVariable, stmt.name)
                val ty = stmt.annotatedType?.let { ensureNamed(it) }
                val initTy = stmt.init?.let { typeOf(it) }
                val finalTy = when {
                    ty != null && initTy != null -> {
                        if(ty.name != initTy.name) error(stmt.span, ErrorCode.TypeMismatch, ty.name, initTy.name)
                        ty
                    }

                    ty != null -> ty
                    initTy != null -> initTy
                    else -> error(stmt.span, ErrorCode.VarNeedsType, stmt.name)
                }

                if(stmt.isConst && stmt.init == null) error(stmt.span, ErrorCode.ConstNeedsInit, stmt.name)
                declare(stmt.name, finalTy, stmt.isConst, stmt.span)
                types.varTypes[currentFn to stmt.name] = finalTy
            }

            is Assign -> {
                val v = resolve(stmt.name) ?: error(stmt.span, ErrorCode.UndefinedVariable, stmt.name)
                if(v.isConst) error(stmt.span, ErrorCode.AssignToConst, stmt.name)
                val rhsTy = typeOf(stmt.value)
                if(rhsTy.name != v.type.name) error(stmt.span, ErrorCode.TypeMismatch, v.type.name, rhsTy.name)
            }

            is ExprStmt -> { typeOf(stmt.expr) }
            is IfStmt -> {
                stmt.branches.forEach { br ->
                    val cTy = typeOf(br.condition)
                    if(cTy.name != "bool") error(br.condition.span, ErrorCode.NonBoolCondition, cTy.name)
                    checkBlock(br.body)
                }

                stmt.elseBranch?.let { checkBlock(it) }
            }

            is WhileStmt -> {
                val cTy = typeOf(stmt.condition)
                if(cTy.name != "bool") error(stmt.condition.span, ErrorCode.NonBoolCondition, cTy.name)
                checkBlock(stmt.body)
            }
        }
    }

    private fun typeOf(e: Expr): NamedType {
        val ty = when(e) {
            is IntLit -> NamedType("int", e.span)
            is FloatLit -> NamedType("float", e.span)
            is BoolLit -> NamedType("bool", e.span)
            is CharLit -> NamedType("char", e.span)
            is StringLit -> NamedType("string", e.span)

            is Ident -> {
                val v = resolve(e.name) ?: error(e.span, ErrorCode.UndefinedVariable, e.name)
                v.type
            }

            is Unary -> when(e.op) {
                UnOp.Not -> {
                    val t = typeOf(e.expr)
                    if(t.name != "bool") error(e.span, ErrorCode.NotConditionBool, "!", t.name)
                    NamedType("bool", e.span)
                }
            }

            is Binary -> {
                val lt = typeOf(e.left)
                val rt = typeOf(e.right)

                val out: NamedType = when(e.op) {
                    BinOp.And, BinOp.Or -> {
                        if(lt.name != "bool" || rt.name != "bool") error(e.span, ErrorCode.LogicNeedsBool, e.op.name)
                        NamedType("bool", e.span)
                    }

                    BinOp.Eq, BinOp.Ne, BinOp.Lt, BinOp.Le, BinOp.Gt, BinOp.Ge -> {
                        val okSame = lt.name == rt.name
                        val okNumMix = setOf(lt.name, rt.name) == setOf("int", "float")
                        val compTy = when {
                            okSame -> lt.name
                            okNumMix -> "float"
                            else -> error(e.span, ErrorCode.CompareTypeMismatch, lt.name, rt.name)
                        }

                        if(e.op == BinOp.Eq || e.op == BinOp.Ne) NamedType("bool", e.span)
                        else {
                            if(compTy !in listOf("int", "float", "char")) error(e.span, ErrorCode.RelopTypeInvalid, e.op.name, compTy)
                            NamedType("bool", e.span)
                        }
                    }

                    else -> {
                        if(e.op == BinOp.Add && (lt.name == "string" || rt.name == "string")) {
                            NamedType("string", e.span)
                        } else {
                            val same = lt.name == rt.name
                            val bothNum = lt.name in listOf("int", "float") && rt.name in listOf("int", "float")
                            if(!same && !bothNum) error(e.span, ErrorCode.TypeMismatch, lt.name, rt.name)
                            val resName = if (lt.name == "float" || rt.name == "float") "float" else lt.name
                            if(resName !in listOf("int", "float")) error(e.span, ErrorCode.InvalidType, resName)
                            NamedType(resName, e.span)
                        }
                    }
                }

                types.exprTypes[e] = out
                out
            }

            is Call -> {
                //TODO: Make this better for when we have more internal functions
                if(e.callee == "print" || e.callee == "println") {
                    if(e.args.size != 1) error(e.span, ErrorCode.ArityMismatch, e.callee, "${e.args.size}", "1")
                    val argTy = typeOf(e.args[0])
                    when(argTy.name) {
                        "int", "float", "bool", "char", "string" -> {}
                        else -> error(e.args[0].span, ErrorCode.UnsupportedPrintType, argTy.name)
                    }

                    val ret = NamedType("int", e.span)
                    types.exprTypes[e] = ret
                    return ret
                }

                if(e.callee == "input") {
                    if(e.args.size != 1) error(e.span, ErrorCode.ArityMismatch, e.callee, "${e.args.size}", "1")
                    val pTy = typeOf(e.args[0])
                    if(pTy.name != "string") error(e.args[0].span, ErrorCode.TypeMismatch, "string", pTy.name)
                    val ret = NamedType("string", e.span)
                    types.exprTypes[e] = ret

                    return ret
                }

                val sig = functions[e.callee] ?: error(e.span, ErrorCode.UnknownFunction, e.callee)
                val (paramTys, retTy) = sig
                if(e.args.size != paramTys.size) error(e.span, ErrorCode.ArityMismatch, e.callee, "${e.args.size}", "${paramTys.size}")

                e.args.forEachIndexed { idx, arg ->
                    val got = typeOf(arg)
                    val want = paramTys[idx]
                    if(got.name != want.name) error(arg.span, ErrorCode.TypeMismatch, want.name, got.name)
                }

                retTy ?: NamedType("int", e.span)
            }

            is MethodCall -> {
                if (e.args.isNotEmpty()) error(e.span, ErrorCode.UnsupportedConversion, "method ${e.method}", "no-args")

                val recvTy = typeOf(e.receiver)
                val out: NamedType = when (e.method) {
                    "toString" -> NamedType("string", e.span)

                    "toInt" -> when (recvTy.name) {
                        "int", "float", "string", "char", "bool" -> NamedType("int", e.span)
                        else -> error(e.span, ErrorCode.UnsupportedConversion, recvTy.name, "int")
                    }

                    "toFloat" -> when (recvTy.name) {
                        "float", "int", "string", "char", "bool" -> NamedType("float", e.span)
                        else -> error(e.span, ErrorCode.UnsupportedConversion, recvTy.name, "float")
                    }

                    "toBool" -> when (recvTy.name) {
                        "bool", "int", "float", "char", "string" -> NamedType("bool", e.span)
                        else -> error(e.span, ErrorCode.UnsupportedConversion, recvTy.name, "bool")
                    }

                    "toChar" -> when (recvTy.name) {
                        "char", "int", "string", "bool", "float" -> NamedType("char", e.span)
                        else -> error(e.span, ErrorCode.UnsupportedConversion, recvTy.name, "char")
                    }

                    else -> error(e.span, ErrorCode.UnknownMethod, e.method)
                }

                types.exprTypes[e] = out
                out
            }
        }

        types.exprTypes[e] = ty
        return ty
    }

    private fun pushScope() = env.addLast(linkedMapOf())
    private fun popScope() = env.removeLast()
    private fun current(): LinkedHashMap<String, VarInfo> = env.lastOrNull() ?: run { pushScope(); env.last() }
    private fun declare(name: String, ty: NamedType, isConst: Boolean, span: Span) {
        current()[name] = VarInfo(ty, isConst, span)
    }

    private fun resolve(name: String): VarInfo? {
        for(scope in env.asReversed()) scope[name]?.let { return it }
        return null
    }

    private fun error(span: Span, code: ErrorCode, vararg args: String): Nothing {
        throw CoalError(Diagnostic(Severity.ERROR, code, fileName, span, args.toList()))
    }

    private fun ensureNamed(t: TypeRef): NamedType = t as? NamedType ?: error(t.span, ErrorCode.InvalidType, "<non-named>")
}