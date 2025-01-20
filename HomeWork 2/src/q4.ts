import { Exp, makePrimOp, makeVarDecl, makeVarRef, Program } from '../imp/L3-ast';
import { Result, makeFailure , makeOk} from '../shared/result';
import { isCExp, isLetExp, isExp,DefineExp, AppExp } from '../imp/L3-ast';
import { BoolExp, CExp,LetExp ,IfExp, Binding, LitExp } from '../imp/L3-ast';
import { isAppExp,isAtomicExp, isBoolExp, isDefineExp, isIfExp, isLitExp, isNumExp,
             isPrimOp, isProcExp, isProgram , isStrExp,isVarRef} from '../imp/L3-ast';
import { makeNumExp, makeProcExp, makeStrExp, makeProgram, makeDefineExp, makeIfExp 
    ,makeAppExp, ProcExp, VarDecl} from '../imp/L3-ast';
import { valueToString} from "../imp/L3-value";
import { isSymbolSExp, isEmptySExp, isCompoundSExp } from "../imp/L3-value";
import { and, map } from "ramda";
import { join } from 'path';
import exp from 'constants';
import { PrimOp } from './L31-ast';

/*
Purpose: Transform L3 AST to JavaScript program string
Signature: l30ToJS(l2AST)
Type: [EXP | Program] => Result<string>
*/
export const l30ToJS = (exp: Exp | Program): Result<string>  =>
    isExp(exp) ? makeOk(l30ToJS2(exp)) :
    isProgram(exp) ? makeOk(map(l30ToJS2, exp.exps).join(";\n")) :
    makeFailure("Never");

const l30ToJS2 = (exp: Exp | Program): string  => 
isBoolExp(exp) ? valueToString(exp.val) :
isNumExp(exp) ? valueToString(exp.val) :
isStrExp(exp) ? valueToString(exp.val):
isLitExp(exp) ? `Symbol.for("${valueToString(exp.val)}")` :
isVarRef(exp) ? exp.var :
isProcExp(exp) ?l30ToJSProcExp(exp) :
isIfExp(exp) ? `(${l30ToJS2(exp.test)} ? ${l30ToJS2(exp.then)} : ${l30ToJS2(exp.alt)})` :
isAppExp(exp) ? isPrimitiveRator(exp.rator)?`(${l30ToJSApExps(exp.rator, exp.rands)})`:l30ToJSApFuns(exp.rator, exp.rands) :
isPrimOp(exp) ? l30ToJSPrimOpExp(exp) :
isLetExp(exp) ? l30ToJS2(rewriteLet(exp)) :
isDefineExp(exp) ? `const ${exp.var.var} = ${l30ToJS2(exp.val)}`:
isProgram(exp) ? `(L3 ${l30ToJSLExps(exp.exps)})` :
exp;


const l30ToJSPrimOpExp = (exp: PrimOp): string =>
    exp.op === "=" || exp.op === "string=?"? "===" : 
    exp.op === "symbol?" ? "((x) => (typeof (x) === symbol))" :
    exp.op === "boolean?" ? "((x) => (typeof (x) === boolean))" :
    exp.op === "string?" ? "((x) => (typeof (x) === string))" :
    exp.op === "number?" ? "((x) => (typeof (x) === number))" :
    exp.op;

const l30ToJSApExps = (rator:CExp, rands:Exp[]): string =>
    isPrimitiveNot(rator)? `!${map(l30ToJS2, rands).join("")}` :map(l30ToJS2, rands).join(` ${l30ToJS2(rator)} `);

const l30ToJSApFuns = (rator:Exp, rands:Exp[]): string =>
    `${l30ToJS2(rator)}(${map((x)=> l30ToJS2(x),rands ).join(",")})`;

const isPrimitiveNot = (x: CExp): boolean => isPrimOp(x)? x.op === "not": false;
const isPrimitiveRator = (x: CExp): boolean => isPrimOp(x)? isPrimitiveOp(x.op): false;
const isPrimitiveOp = (x: string): boolean =>
    ["+", "-", "*", "/", ">", "<", "=", "not", "and", "or",
     "eq?", "string=?","number?", "boolean?", "symbol?", "string?"].includes(x);
const l30ToJSLExps = (les: Exp[]): string => map(l30ToJS2, les).join(" ");
const l30ToJSProcExp = (pe: ProcExp): string => 
    `((${map((p: VarDecl) => p.var, pe.args).join(",")}) => ${l30ToJSLExps(pe.body)})`


const rewriteLet = (e: LetExp): AppExp => {
    const vars = map((b) => b.var, e.bindings);
    const vals = map((b) => b.val, e.bindings);
    return makeAppExp(
            makeProcExp(vars, e.body),
            vals);
}