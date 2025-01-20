import {  Exp, makeBinding, makeLetExp, Program } from "./L31-ast";
import { Result, makeFailure,makeOk } from "../shared/result";
import { isCExp, isLetExp, isExp,DefineExp } from "./L31-ast";
import { BoolExp, CExp,LetExp,LetPlusExp ,IfExp, Binding ,makeLetPlusExp, isLetPlusExp} from "./L31-ast";
import { isAppExp,isAtomicExp, isBoolExp, isDefineExp, isIfExp, isLitExp, isNumExp,
             isPrimOp, isProcExp, isProgram , unparseL31} from "./L31-ast";
import { makeNumExp, makeProcExp, makeStrExp, makeProgram, makeDefineExp, makeIfExp 
,makeAppExp} from "./L31-ast";
import { first, isEmpty, rest} from "../shared/list";
import { map } from "ramda";
/*
Purpose: Transform L31 AST to L3 AST
Signature: l31ToL3(l31AST)
Type: [Exp | Program] => Result<Exp | Program>
*/
export const L31ToL3 = (exp: Exp | Program): Result<Exp | Program> =>
    isExp(exp) ? makeOk(L31ToL3Exp(exp)) :
    isProgram(exp) ? makeOk(makeProgram(map(L31ToL3Exp, exp.exps))) :
    makeOk(exp);

const fromLetPToLet = (exp: LetPlusExp): LetExp =>
(isEmpty(exp.bindings) || exp.bindings.length === 1)? makeLetExp(exp.bindings,exp.body):
makeLetExp([first(exp.bindings)], [fromLetPToLet(makeLetPlusExp(rest(exp.bindings), map(L31ToL3CExp, exp.body)))]);

const L31ToL3Exp = (exp: Exp): Exp => isCExp(exp) ? L31ToL3CExp(exp) :
isDefineExp(exp) ? makeDefineExp(exp.var, L31ToL3CExp(exp.val)) :
exp;

const L31ToL3CExp = (exp: CExp): CExp =>
    isAtomicExp(exp) ? exp :
    isLitExp(exp) ? exp :
    isIfExp(exp) ? makeIfExp(L31ToL3CExp(exp.test),
    L31ToL3CExp(exp.then),
    L31ToL3CExp(exp.alt)) :
    isAppExp(exp) ? makeAppExp(L31ToL3CExp(exp.rator),
                               map(L31ToL3CExp, exp.rands)) :
    isProcExp(exp) ? makeProcExp(exp.args, map(L31ToL3CExp, exp.body)) :
    isLetExp(exp) ? makeLetExp(exp.bindings,map(L31ToL3CExp, exp.body)) :
    isLetPlusExp(exp) ? L31ToL3CExp(fromLetPToLet(exp)) :
    exp;

