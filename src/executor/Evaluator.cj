package cjcj.executor

import cjcj.visitor.*
import cjcj.scanner.TokenKind
import cjcj.scanner.Token
import std.convert.*
import cjcj.visitor.Environment
import std.deriving.Derive

// --- Lab 1 辅助类型 ---

/**
 * 运行时类型枚举
 * 用于类型比较
 */
@Derive[Equatable]
private enum CjType {
    | CjInt64
    | CjString
    | CjBool
    | CjUnit
    | CjAny
}

extend CjType <: ToString {
    public func toString(): String {
        match (this) {
            case CjInt64 => "Int64"
            case CjString => "String"
            case CjBool => "Bool"
            case CjUnit => "Unit"
            case CjAny => "Any"
        }
    }
}

/**
 * 变量状态
 * 区分已初始化和未初始化的变量
 */
private enum VarState {
    | UNINITIALIZED(CjType) // 未初始化
    | INITIALIZED(Value)  // 已初始化
}

/**
 * 存储在环境中的变量信息
 * 包含可变性(let/var)和当前状态
 */
private class Variable {
    public let isMutable: Bool
    public var state: VarState

    public init(isMutable: Bool, state: VarState) {
        this.isMutable = isMutable
        this.state = state
    }
}

// --- Lab 1 控制流异常 ---

/**
 * 用于 'break' 的异常
 */
private class BreakException <: Exception {}

/**
 * 用于 'continue' 的异常
 */
private class ContinueException <: Exception {}


class Lab1TodoException <: Exception {
    public init(message: String) {
        super("Lab 1 TODO: " + message)
    }
}

/**
 * Evaluator Visitor
 *
 * Lab 1 实现
 */
public open class Evaluator <: Visitor<Value> {
    
    // 变量环境，用于实现静态作用域
    private var env: Environment<String, Variable> = Environment()
    
    // 循环深度，用于检查 break/continue 是否在循环内
    private var loopDepth: Int = 0

    // --- 辅助函数 ---

    /**
     * 从 Value 获取 CjType
     */
    private func getCjType(val: Value): CjType {
        match (val) {
            case VInteger(_) => CjInt64
            case VString(_) => CjString
            case VBoolean(_) => CjBool
            case VUnit => CjUnit
        }
    }

    /**
     * 检查运行时值的类型是否匹配声明的类型
     * CjAny 匹配所有类型
     */
    private func typeMatches(expected: CjType, actual: Value): Bool {
        if (expected == CjAny) {
            return true
        }
        return getCjType(actual) == expected
    }

    /**
     * 从 AST TypeNode 获取 CjType
     */
    private func getCjTypeFromNode(node: TypeNode): CjType {
        match (node.typeName.value) {
            case "Int64" => CjInt64
            case "String" => CjString
            case "Bool" => CjBool
            case "Unit" => CjUnit
            case _ => CjAny // 对于 Lab 1，只支持这四种
        }
    }

    /**
     * 在新的作用域中执行一个块
     */
    private func visitBlockInNewScope(block: Block): Value {
        let previousEnv = this.env
        this.env = Environment(previousEnv)
        try {
            let result = block.traverse(this)
            this.env = previousEnv // 恢复父作用域
            return result
        } catch (e: Exception) {
            this.env = previousEnv // 确保异常时也能恢复
            throw e
        }
    }

    /**
     * 整数乘方 (a ** b)
     */
    private func intPow(base: Int64, exp: Int64, node: Node): Int64 {
        if (exp < 0) {
            throw CjcjRuntimeErrorWithLocation(ErrorCode.EXP_NEGATIVE_POWER, "exponent cannot be negative", node)
        }
        if (exp == 0) { return 1 }
        
        var res: Int64 = 1
        var b = base
        var e = exp
        
        try {
            // 快速幂算法
            while (e > 0) {
                if (e % 2 == 1) {
                    res = res * b
                }
                if (e > 1) { // 避免最后一次不必要的平方
                    b = b * b
                }
                e = e / 2
            }
        } catch (e: OverflowException) {
            throw CjcjRuntimeErrorWithLocation(ErrorCode.EXP_OVERFLOW, "exponentiation overflow", node)
        }
        return res
    }

    /**
     * 字符串重复 (String * Int64)
     */
    private func stringRepeat(s: String, times: Int64, node: Node): String {
        if (times < 0) {
            // PDF 未定义，但重复负数次无意义，按乘法类型错误处理
            throw CjcjRuntimeErrorWithLocation(ErrorCode.MUL_TYPE_MISMATCH, "string repeat count cannot be negative", node)
        }
        if (times == 0) { return "" }
        
        let builder = StringBuilder()
        for (_ in 0..times) {
            builder.append(s)
        }
        return builder.toString()
    }

    /**
     * 检查两个 Value 是否相等 (==)
     */
    private func areEqual(left: Value, right: Value, node: Node): Bool {
        match ((left, right)) {
            case (VInteger(a), VInteger(b)) => a == b
            case (VString(a), VString(b)) => a == b
            case (VBoolean(a), VBoolean(b)) => a == b
            case (VUnit, VUnit) => true
            // 类型不同，报错
            case _ =>
                let op = (node as BinaryExpr).getOrThrow().oper.kind
                let code = if (op == TokenKind.EQUAL) { ErrorCode.EQ_TYPE_MISMATCH } else { ErrorCode.NEQ_TYPE_MISMATCH }
                throw CjcjRuntimeErrorWithLocation(code,
                    "cannot compare ${getCjType(left)}(${left.toValueString()}) and ${getCjType(right)}(${right.toValueString()}) for equality", node)
        }
    }

    // --- Visitor 实现 ---

    public open override func visit(_: Program): Value {
        // Executor.cj 负责调用 main 块，这里不需实现
        throw UnsupportedException("Unimplemented method for Visitor : Program")
    }

    /**
     * 二元表达式 (Section 4.3)
     */
    public open override func visit(expr: BinaryExpr): Value {
        
        // 1. 处理逻辑运算符的短路特性
        if (expr.oper.kind == TokenKind.OR) {
            let left = expr.left.traverse(this)
            match (left) {
                case VBoolean(b) =>
                    if (b) { return Value.VBoolean(true) } // 短路
                    // left 为 false，计算 right
                    let right = expr.right.traverse(this)
                    match (right) {
                        case VBoolean(b2) => return Value.VBoolean(b2)
                        case _ => throw CjcjRuntimeErrorWithLocation(ErrorCode.OR_TYPE_MISMATCH,
                            "right side of '||' must be Bool, but got ${getCjType(right)}(${right.toValueString()})", expr)
                    }
                case _ => throw CjcjRuntimeErrorWithLocation(ErrorCode.OR_TYPE_MISMATCH,
                    "left side of '||' must be Bool, but got ${getCjType(left)}(${left.toValueString()})", expr)
            }
        }

        if (expr.oper.kind == TokenKind.AND) {
            let left = expr.left.traverse(this)
            match (left) {
                case VBoolean(b) =>
                    if (!b) { return Value.VBoolean(false) } // 短路
                    // left 为 true，计算 right
                    let right = expr.right.traverse(this)
                    match (right) {
                        case VBoolean(b2) => return Value.VBoolean(b2)
                        case _ => throw CjcjRuntimeErrorWithLocation(ErrorCode.AND_TYPE_MISMATCH,
                            "right side of '&&' must be Bool, but got ${getCjType(right)}(${right.toValueString()})", expr)
                    }
                case _ => throw CjcjRuntimeErrorWithLocation(ErrorCode.AND_TYPE_MISMATCH,
                    "left side of '&&' must be Bool, but got ${getCjType(left)}(${left.toValueString()})", expr)
            }
        }

        // 2. 其他运算符，先计算两边
        let left = expr.left.traverse(this)
        let right = expr.right.traverse(this)

        try {
            match (expr.oper.kind) {
                // --- 算术运算 ---
                case TokenKind.ADD => match ((left, right)) {
                    case (VInteger(a), VInteger(b)) => Value.from(a + b)
                    case (VString(a), VString(b)) => Value.from(a + b)
                    case _ => throw CjcjRuntimeErrorWithLocation(ErrorCode.ADD_TYPE_MISMATCH,
                        "cannot add ${getCjType(left)}(${left.toValueString()}) and ${getCjType(right)}(${right.toValueString()})", expr)
                }
                case TokenKind.SUB => match ((left, right)) {
                    case (VInteger(a), VInteger(b)) => Value.from(a - b)
                    case _ => throw CjcjRuntimeErrorWithLocation(ErrorCode.SUB_TYPE_MISMATCH,
                        "cannot subtract ${getCjType(right)}(${right.toValueString()}) from ${getCjType(left)}(${left.toValueString()})", expr)
                }
                case TokenKind.MUL => match ((left, right)) {
                    case (VInteger(a), VInteger(b)) => Value.from(a * b)
                    case (VString(a), VInteger(b)) => Value.from(stringRepeat(a, b, expr))
                    case (VInteger(a), VString(b)) => Value.from(stringRepeat(b, a, expr))
                    case _ => throw CjcjRuntimeErrorWithLocation(ErrorCode.MUL_TYPE_MISMATCH,
                        "cannot multiply ${getCjType(left)}(${left.toValueString()}) and ${getCjType(right)}(${right.toValueString()})", expr)
                }
                case TokenKind.DIV => match ((left, right)) {
                    case (VInteger(a), VInteger(b)) =>
                        if (b == 0) {
                            throw CjcjRuntimeErrorWithLocation(ErrorCode.DIV_BY_ZERO, "division by zero", expr)
                        }
                        Value.from(a / b) // 整数除法
                    case _ => throw CjcjRuntimeErrorWithLocation(ErrorCode.DIV_TYPE_MISMATCH,
                        "cannot divide ${getCjType(left)}(${left.toValueString()}) by ${getCjType(right)}(${right.toValueString()})", expr)
                }
                case TokenKind.MOD => match ((left, right)) {
                    case (VInteger(a), VInteger(b)) =>
                        if (b == 0) {
                            throw CjcjRuntimeErrorWithLocation(ErrorCode.MOD_BY_ZERO, "modulo by zero", expr)
                        }
                        Value.from(a % b)
                    case _ => throw CjcjRuntimeErrorWithLocation(ErrorCode.MOD_TYPE_MISMATCH,
                        "cannot modulo ${getCjType(left)}(${left.toValueString()}) by ${getCjType(right)}(${right.toValueString()})", expr)
                }
                case TokenKind.EXP => match ((left, right)) {
                    case (VInteger(a), VInteger(b)) => Value.from(intPow(a, b, expr))
                    case _ => throw CjcjRuntimeErrorWithLocation(ErrorCode.EXP_TYPE_MISMATCH,
                        "cannot exponentiate ${getCjType(left)}(${left.toValueString()}) by ${getCjType(right)}(${right.toValueString()})", expr)
                }

                // --- 比较运算 ---
                case TokenKind.LT => match ((left, right)) {
                    case (VInteger(a), VInteger(b)) => Value.VBoolean(a < b)
                    case (VString(a), VString(b)) => Value.VBoolean(a < b)
                    case _ => throw CjcjRuntimeErrorWithLocation(ErrorCode.CMP_TYPE_MISMATCH,
                        "cannot compare ${getCjType(left)}(${left.toValueString()}) and ${getCjType(right)}(${right.toValueString()}) with '<'", expr)
                }
                case TokenKind.LE => match ((left, right)) {
                    case (VInteger(a), VInteger(b)) => Value.VBoolean(a <= b)
                    case (VString(a), VString(b)) => Value.VBoolean(a <= b)
                    case _ => throw CjcjRuntimeErrorWithLocation(ErrorCode.CMP_TYPE_MISMATCH,
                        "cannot compare ${getCjType(left)}(${left.toValueString()}) and ${getCjType(right)}(${right.toValueString()}) with '<='", expr)
                }
                case TokenKind.GT => match ((left, right)) {
                    case (VInteger(a), VInteger(b)) => Value.VBoolean(a > b)
                    case (VString(a), VString(b)) => Value.VBoolean(a > b)
                    case _ => throw CjcjRuntimeErrorWithLocation(ErrorCode.CMP_TYPE_MISMATCH,
                        "cannot compare ${getCjType(left)}(${left.toValueString()}) and ${getCjType(right)}(${right.toValueString()}) with '>'", expr)
                }
                case TokenKind.GE => match ((left, right)) {
                    case (VInteger(a), VInteger(b)) => Value.VBoolean(a >= b)
                    case (VString(a), VString(b)) => Value.VBoolean(a >= b)
                    case _ => throw CjcjRuntimeErrorWithLocation(ErrorCode.CMP_TYPE_MISMATCH,
                        "cannot compare ${getCjType(left)}(${left.toValueString()}) and ${getCjType(right)}(${right.toValueString()}) with '>='", expr)
                }

                // --- 相等运算 ---
                case TokenKind.EQUAL => Value.VBoolean(areEqual(left, right, expr))
                case TokenKind.NOTEQ => Value.VBoolean(!areEqual(left, right, expr))
                
                case _ => throw Lab1TodoException("Unimplemented Binary Operator `${expr.oper.kind}`")
            }
        } catch (e: OverflowException) {
            // 捕获 Int64 溢出
            let code = match (expr.oper.kind) {
                case TokenKind.ADD => ErrorCode.ADD_OVERFLOW
                case TokenKind.SUB => ErrorCode.SUB_OVERFLOW
                case TokenKind.MUL => ErrorCode.MUL_OVERFLOW
                case _ => ErrorCode.EXP_OVERFLOW // 假设其他溢出是乘方
            }
            throw CjcjRuntimeErrorWithLocation(code,
                "arithmetic overflow for ${expr.oper.value}", expr)
        }
    }

    /**
     * 一元表达式 (Section 4.4)
     */
    public open override func visit(expr: UnaryExpr): Value {
        let right = expr.right.traverse(this)
        match (expr.oper.kind) {
            case TokenKind.SUB => // 取负
                match (right) {
                    case VInteger(i) =>
                        if (i == Int64.Min) {
                            throw CjcjRuntimeErrorWithLocation(ErrorCode.NEG_OVERFLOW, "negation overflow", expr)
                        }
                        return Value.VInteger(-i)
                    case _ =>
                        throw CjcjRuntimeErrorWithLocation(ErrorCode.NEG_TYPE_MISMATCH,
                            "unary '-' cannot be applied to type ${getCjType(right)}(${right.toValueString()})", expr)
                }
            case TokenKind.NOT => // 取非
                match (right) {
                    case VBoolean(b) => return Value.VBoolean(!b)
                    case _ =>
                        throw CjcjRuntimeErrorWithLocation(ErrorCode.NOT_TYPE_MISMATCH,
                            "'!' cannot be applied to type ${getCjType(right)}(${right.toValueString()})", expr)
                }
            case _ => throw Lab1TodoException("Unary Operator `${expr.oper.kind}`")
        }
    }

    /**
     * 括号表达式
     */
    public open override func visit(par: ParenExpr): Value {
        return par.parenthesizedExpr.traverse(this) // 只需计算内部表达式
    }

    /**
     * 字面量 (Section 2.2)
     */
    public open override func visit(lit: LitConstExpr): Value {
        match (lit.literal.kind) {
            case TokenKind.INTEGER_LITERAL => Value.from(Int64.parse(lit.literal.value))
            case TokenKind.STRING_LITERAL => Value.from(lit.literal.value)
            case TokenKind.BOOL_LITERAL => Value.from(lit.literal.value == "true")
            case TokenKind.UNIT_LITERAL => Value.VUnit
            case _ => throw Lab1TodoException("There are more literal types to implement: ${lit.literal.kind}")
        }
    }

    /**
     * 赋值表达式 (Section 4.7)
     */
    public open override func visit(expr: AssignExpr): Value {
        // Lab 1 保证左侧是 RefExpr
        if (let Some(ref) <- (expr.left as RefExpr)) {
            let varName = ref.identifier.value
            let rightVal = expr.right.traverse(this)

            // 递归查找变量
            if (let Some(variable) <- env.getGlobal(varName)) {
                match (variable.state) {
                    case INITIALIZED(oldValue) =>
                        if (!variable.isMutable) {
                            // 错误：给 'let' 赋值
                            throw CjcjRuntimeErrorWithLocation(ErrorCode.ASSGIN_IMMUT_VAR,
                                "cannot assign to immutable variable '${varName}'", expr)
                        }
                        
                        // 检查 'var' 的类型
                        if (getCjType(oldValue) != getCjType(rightVal)) {
                            throw CjcjRuntimeErrorWithLocation(ErrorCode.ASSIGN_TYPE_MISMATCH,
                                "cannot assign value of type ${getCjType(rightVal)}(${rightVal.toValueString()}) to variable '${varName}' of type ${getCjType(oldValue)}", expr)
                        }

                        // 赋值
                        variable.state = VarState.INITIALIZED(rightVal)
                        return Value.VUnit

                    case UNINITIALIZED(expectedType) =>
                        // 这是 'let a: T' 或 'var a: T' 的第一次赋值
                        
                        // 检查类型
                        if (expectedType != CjAny && !typeMatches(expectedType, rightVal)) {
                             let errCode = if (variable.isMutable) { ErrorCode.ASSIGN_TYPE_MISMATCH } else { ErrorCode.DEF_TYPE_MISMATCH }
                             throw CjcjRuntimeErrorWithLocation(errCode,
                                "cannot assign value of type ${getCjType(rightVal)}(${rightVal.toValueString()}) to uninitialized variable '${varName}' of type ${expectedType}", expr)
                        }

                        // 'let' 只能赋值一次
                        if (!variable.isMutable) {
                           variable.state = VarState.INITIALIZED(rightVal) // 变为已初始化
                           return Value.VUnit
                        } else {
                           // 'var' 赋值
                           variable.state = VarState.INITIALIZED(rightVal)
                           return Value.VUnit
                        }
                }
            } else {
                throw CjcjRuntimeErrorWithLocation(ErrorCode.UNDEFINED_VAR,
                    "variable '${varName}' is not defined", expr)
            }
        } else {
            // Lab 1 语法保证不会到这里
            throw CjcjRuntimeErrorWithLocation(ErrorCode.UNDEFINED_VAR, "invalid assignment target", expr)
        }
    }

    /**
     * 变量引用 (Section 4.9)
     */
    public open override func visit(ref: RefExpr): Value {
        let varName = ref.identifier.value
        
        // 递归查找
        if (let Some(variable) <- env.getGlobal(varName)) {
            match (variable.state) {
                case INITIALIZED(value) => return value // 返回存储的值
                case UNINITIALIZED(_) =>
                    // 错误：读取未初始化的变量
                    throw CjcjRuntimeErrorWithLocation(ErrorCode.UNINITIALIZED_VAR,
                        "variable '${varName}' is read before being initialized", ref)
            }
        } else {
            // 错误：未定义变量
            throw CjcjRuntimeErrorWithLocation(ErrorCode.UNDEFINED_VAR,
                "variable '${varName}' is not defined", ref)
        }
    }

    /**
     * 表达式块 (Section 4.2)
     */
    public open override func visit(block: Block): Value {
        var ret = Value.VUnit
        for (stmt in block.nodes.iterator()) {
            ret = stmt.traverse(this) // 依次执行，保留最后一个值
        }
        return ret
    }

    /**
     * If 表达式 (Section 4.5)
     */
    public open override func visit(expr: IfExpr): Value {
        let condVal = expr.condition.traverse(this)
        
        let condBool: Bool
        match (condVal) {
            case VBoolean(b) => condBool = b
            case _ => throw CjcjRuntimeErrorWithLocation(ErrorCode.IF_TYPE_MISMATCH,
                "if condition must be Bool, but got ${getCjType(condVal)}(${condVal.toValueString()})", expr)
        }

        if (condBool) {
            // 执行 ifBlock (在新作用域中)
            return visitBlockInNewScope(expr.ifBlock)
        } else {
            // Parser 保证了 elseBranch 总是存在
            // (if-then 被 desugar 成 if-then-else-unit)
            
            // 执行 elseBranch
            // 如果 else 分支是另一个 block，它也需要新作用域
            if (let Some(block) <- (expr.elseBranch as Block)) {
                return visitBlockInNewScope(block)
            } else {
                // 这是 'else if' 的情况
                return expr.elseBranch.traverse(this)
            }
        }
    }

    /**
     * While 表达式 (Section 4.6)
     */
    public open override func visit(expr: WhileExpr): Value {
        while (true) {
            // 1. 计算 cond
            let condVal = expr.condition.traverse(this)
            
            let condBool: Bool
            match (condVal) {
                case VBoolean(b) => condBool = b
                case _ => throw CjcjRuntimeErrorWithLocation(ErrorCode.WHILE_TYPE_MISMATCH,
                    "while condition must be Bool, but got ${getCjType(condVal)}(${condVal.toValueString()})", expr.condition)
            }

            if (!condBool) {
                break // 结束循环
            }
            
            // 2. 计算 body
            loopDepth++
            try {
                // 在新作用域中执行 body
                visitBlockInNewScope(expr.block) 
            } catch (e: BreakException) {
                // 捕获 break
                loopDepth--
                break // 退出 while(true)
            } catch (e: ContinueException) {
                // 捕获 continue
                // 自动进入下一次循环
            } catch (e: Exception) {
                loopDepth-- // 保证异常安全
                throw e
            }
            loopDepth--
        }
        return Value.VUnit // while 表达式返回 Unit
    }

    public open override func visit(call: CallExpr): Value {
        // Lab 1 不需要
        throw UnsupportedException("Unimplemented method for Visitor : Call Expression")
    }

    public open override func visit(_: ReturnExpr): Value {
        // Lab 1 不需要
        throw UnsupportedException("Unimplemented method for Visitor : Return Expression")
    }

    /**
     * Jump 表达式 (break/continue) (Section 4.6.1)
     */
    public open override func visit(jmp: JumpExpr): Value {
        if (loopDepth == 0) {
            // 检查是否在循环内
            let (code, msg) = if (jmp.keyword.kind == TokenKind.BREAK) {
                (ErrorCode.BREAK_OUTSIDE_LOOP, "break used outside of a loop")
            } else {
                (ErrorCode.CONTINUE_OUTSIDE_LOOP, "continue used outside of a loop")
            }
            throw CjcjRuntimeErrorWithLocation(code, msg, jmp)
        }

        // 抛出控制流异常
        if (jmp.keyword.kind == TokenKind.BREAK) {
            throw BreakException()
        } else { // CONTINUE
            throw ContinueException()
        }
    }

    /**
     * 变量定义 (Section 4.8)
     */
    public open override func visit(decl: VarDecl): Value {
        let varName = decl.identifier.value
        
        // 检查当前作用域是否重复定义
        if (env.getLocal(varName).isSome()) {
            throw CjcjRuntimeErrorWithLocation(ErrorCode.DUPLICATED_DEF,
                "variable '${varName}' is already defined in this scope", decl)
        }

        let isMutable = (decl.keyword.kind == TokenKind.VAR)
        
        // 获取声明的类型（如果有）
        var expectedType: CjType = CjAny
        if (let Some(typeNode) <- decl.declType) {
            expectedType = getCjTypeFromNode(typeNode)
        }

        if (let Some(initializer) <- decl.initializer) {
            // Case 1: let a = b, var a = b, let a: T = b, var a: T = b
            let initVal = initializer.traverse(this)

            // 检查类型
            if (expectedType != CjAny && !typeMatches(expectedType, initVal)) {
                throw CjcjRuntimeErrorWithLocation(ErrorCode.DEF_TYPE_MISMATCH,
                    "cannot initialize variable '${varName}' of type ${expectedType} with value of type ${getCjType(initVal)}(${initVal.toValueString()})", decl)
            }
            
            let variable = Variable(isMutable, VarState.INITIALIZED(initVal))
            env.declare(varName, variable)
        } else {
            // Case 2: let a: T, var a: T (必须有类型)
            if (decl.declType.isNone()) {
                // 语法上应该不允许 `let a`
                throw CjcjRuntimeErrorWithLocation(ErrorCode.DUPLICATED_DEF, "variable declaration must have type or initializer", decl)
            }
            
            let variable = Variable(isMutable, VarState.UNINITIALIZED(expectedType))
            env.declare(varName, variable)
        }
        
        return Value.VUnit // 变量定义语句返回 Unit
    }

    // --- Lab 1 不需要实现以下方法 ---

    public open override func visit(_: FuncParam): Value {
        throw UnsupportedException("Unimplemented method for Visitor : Function Paramters")
    }

    public open override func visit(_: FuncDecl): Value {
        throw UnsupportedException("Unimplemented method for Visitor : Function Declaration")
    }

    public open override func visit(_: MainDecl): Value {
        // Executor.cj 负责处理 MainDecl
        throw UnsupportedException("Unimplemented method for Visitor : Main Declaration")
    }

    public open override func visit(_: ClassDecl): Value {
        throw UnsupportedException("Unimplemented method for Visitor : Class Declaration")
    }

    public open override func visit(_: Body): Value {
        throw UnsupportedException("Unimplemented method for Visitor : Body")
    }

    public open override func visit(arg: Argument): Value {
        throw UnsupportedException("Unimplemented method for Visitor : Argument")
    }

    public open override func visit(_: TypeNode): Value {
        throw UnsupportedException("Unimplemented method for Visitor : Type Node")
    }

    public open override func visit(_: PrimitiveType): Value {
        throw UnsupportedException("Unimplemented method for Visitor : Primitive Types")
    }

    public open override func visit(_: RefType): Value {
        throw UnsupportedException("Unimplemented method for Visitor : Reference Type")
    }

    public open override func visit(_: VariableReference): Value {
        throw UnsupportedException("Unimplemented method for Visitor : Variable Reference (ASG)")
    }

    public open override func visit(_: FuncReference): Value {
        throw UnsupportedException("Unimplemented method for Visitor : Function Reference (ASG)")
    }

    public open override func visit(_: ClassReference): Value {
        throw UnsupportedException("Unimplemented method for Visitor : Class Reference (ASG)")
    }

    public open override func visit(_: VarDeclWithRef): Value {
        throw UnsupportedException(
            "Unimplemented method for Visitor : Variable Declaration with" + "References Stored (ASG)")
    }

    public open override func visit(_: FuncDeclWithRef): Value {
        // 修复：移除错误的 's'
        throw UnsupportedException(
            "Unimplemented method for Visitor : Function Declaration with" + "References Stored (ASG)")
    }

    public open override func visit(_: MainDeclWithRef): Value {
        throw UnsupportedException(
            "Unimplemented method for Visitor : Main Declaration with" + "References Stored (ASG)")
    }

    public open override func visit(_: ClassDeclWithRef): Value {
        throw UnsupportedException(
            "Unimplemented method for Visitor : Class Declaration with" + "References Stored (ASG)")
    }

    public open override func visit(_: MemberAccess): Value {
        throw UnsupportedException("Unimplemented method for Visitor : Member Access")
    }

    public open override func visit(_: PrimitiveTypeExpr): Value {
        throw UnsupportedException("Unimplemented method for Visitor : Primitive type expression")
    }

    public open override func visit(_: RefExprWithRef): Value {
        throw UnsupportedException("Unimplemented method for Visitor : Reference expression with reference")
    }

    public open override func visit(_: ThisSuperExpr): Value {
        throw UnsupportedException("Unimplemented method for Visitor : This Super expression")
    }

    public open override func visit(_: ThisSuperReference): Value {
        throw UnsupportedException("Unimplemented method for Visitor : This Super reference")
    }

    public open override func visit(_: CallExprWithRef): Value {
        throw UnsupportedException("Unimplemented method for Visitor : Call expression with reference")
    }

    public open override func visit(_: MemberAccessWithRef): Value {
        throw UnsupportedException("Unimplemented method for Visitor : Member access with reference")
    }

    public open override func visit(_: InterfaceDecl): Value {
        throw UnsupportedException("Unimplemented method for Visitor : Interface Declaration")
    }

    public open override func visit(_: InterfaceDeclWithRef): Value {
        throw UnsupportedException("Unimplemented method for Visitor : Interface Declaration with reference")
    }

    public open override func visit(_: InterfaceReference): Value {
        throw UnsupportedException("Unimplemented method for Visitor : Interface Reference")
    }
}