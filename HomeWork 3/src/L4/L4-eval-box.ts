// L4-eval-box.ts
// L4 with mutation (set!) and env-box model
// Direct evaluation of letrec with mutation, define supports mutual recursion.

import { map, repeat, zipWith } from "ramda";
import { isBoolExp, isCExp, isLitExp, isNumExp, isPrimOp, isStrExp, isVarRef, isSetExp,
         isAppExp, isDefineExp, isIfExp, isLetrecExp, isLetExp, isProcExp, Binding, VarDecl, VarRef, CExp, Exp, IfExp, LetrecExp, LetExp, ProcExp, Program, SetExp,
         parseL4Exp, DefineExp, isTraceExp as isTraceExp, TraceExp, makeVarRef} from "./L4-ast";
import { applyEnv, applyEnvBdg, globalEnvAddBinding, makeExtEnv, setFBinding,
            theGlobalEnv, Env, FBinding,getFBindingVal } from "./L4-env-box";
import { isClosure, makeClosure, Closure, Value, valueToString, TracedClosure, isTraceClosure, makeTracedClosure } from "./L4-value-box";
import { applyPrimitive } from "./evalPrimitive-box";
import { first, rest, isEmpty, cons } from "../shared/list";
import { Result, bind, mapv, mapResult, makeFailure, makeOk } from "../shared/result";
import { parse as p } from "../shared/parser";
import { Box , makeBox, unbox, setBox} from '../shared/Box';

// ========================================================
// Eval functions

const applicativeEval = (exp: CExp, env: Env): Result<Value> => {
    // console.log(`applicativeEval => exp: ${JSON.stringify(exp)}`)
    return isNumExp(exp) ? makeOk(exp.val) :
    isBoolExp(exp) ? makeOk(exp.val) :
    isStrExp(exp) ? makeOk(exp.val) :
    isPrimOp(exp) ? makeOk(exp) :
    isVarRef(exp) ? applyEnv(env, exp.var) :
    isLitExp(exp) ? makeOk(exp.val as Value) :
    isIfExp(exp) ? evalIf(exp, env) :
    isProcExp(exp) ? evalProc(exp, env) :
    isLetExp(exp) ? evalLet(exp, env) :
    isLetrecExp(exp) ? evalLetrec(exp, env) :
    isSetExp(exp) ? evalSet(exp, env) :
    isAppExp(exp) ? bind(applicativeEval(exp.rator, env), (proc: Value) =>
                        bind(mapResult((rand: CExp) => applicativeEval(rand, env), exp.rands), (args: Value[]) =>
                            applyProcedure(proc, args))) :
    isTraceExp(exp) ? evalTraceExp(exp) : // HW3
    exp;

}

export const isTrueValue = (x: Value): boolean =>
    ! (x === false);

    
// HW3
 
const evalTraceExp = (exp: TraceExp): Result<void> =>
    bind(applyEnvBdg(theGlobalEnv, exp.var.var), (binding: FBinding) => bind(makeOk(getFBindingVal(binding)),(val: Value) => isClosure(val) 
    ? mapv(makeOk(makeTracedClosure(val, exp.var.var)), (trCl: TracedClosure) => setFBinding(binding,trCl))  
    : makeFailure(`the value of the var ${exp.var.var} is not a closure`)))


// HW3 use these functions
const printPreTrace = (name: string, vals: Value[], counter: number): void =>
    console.log(`>${" >".repeat(counter)} (${name} ${map(valueToString, vals)})`)

const printPostTrace = (val: Value, counter: number): void =>
    console.log(`<${" <".repeat(counter)} ${val}`)


const evalIf = (exp: IfExp, env: Env): Result<Value> =>
    bind(applicativeEval(exp.test, env), (test: Value) => 
        isTrueValue(test) ? applicativeEval(exp.then, env) : 
        applicativeEval(exp.alt, env));

const evalProc = (exp: ProcExp, env: Env): Result<Closure> =>
    makeOk(makeClosure(exp.args, exp.body, env));

// KEY: This procedure does NOT have an env parameter.
//      Instead we use the env of the closure.
const applyProcedure = (proc: Value, args: Value[]): Result<Value> =>
    isPrimOp(proc) ? applyPrimitive(proc, args) :
    isClosure(proc) ? applyClosure(proc, args) :
    isTraceClosure(proc) ? applyTracedClosure(proc, args) :
    makeFailure(`Bad procedure ${JSON.stringify(proc)}`);

const applyClosure = (proc: Closure, args: Value[]): Result<Value> => {
    const vars = map((v: VarDecl) => v.var, proc.params);
    return evalSequence(proc.body, makeExtEnv(vars, args, proc.env));
}

const applyTracedClosure = (proc: TracedClosure, args: Value[]): Result<Value> => {
    printPreTrace(proc.name, args, unbox(proc.counter));
    setBox(proc.counter,unbox(proc.counter) + 1);
    const vars = map((v: VarDecl) => v.var, proc.closure.params);
    const value =  evalSequence(proc.closure.body, makeExtEnv(vars, args, proc.closure.env));
    setBox(proc.counter,unbox(proc.counter) - 1);
    mapv(value,(val: Value) => printPostTrace(val, unbox(proc.counter)));
    return value;
}
    



// Evaluate a sequence of expressions (in a program)
export const evalSequence = (seq: Exp[], env: Env): Result<Value> => {
    // console.log(`evalSequence => exp: ${JSON.stringify(seq)}`)
    return isEmpty(seq) ? makeFailure("Empty program") : evalCExps(first(seq), rest(seq), env);
}
    
const evalCExps = (first: Exp, rest: Exp[], env: Env): Result<Value> =>
    isDefineExp(first) ? evalDefineExps(first, rest) :
    isCExp(first) && isEmpty(rest) ? applicativeEval(first, env) :
    isCExp(first) ? bind(applicativeEval(first, env), _ => evalSequence(rest, env)) :
    first;

// Eval a sequence of expressions when the first exp is a Define.
// Compute the rhs of the define, extend the env with the new binding
// then compute the rest of the exps in the new env.
// L4-BOX @@
// define always updates theGlobalEnv
// We also only expect defineExps at the top level.
const evalDefineExps = (def: DefineExp, exps: Exp[]): Result<Value> =>
    bind(applicativeEval(def.val, theGlobalEnv), (rhs: Value) => { 
            globalEnvAddBinding(def.var.var, rhs);
            return evalSequence(exps, theGlobalEnv); 
        });

// Main program
// L4-BOX @@ Use GE instead of empty-env
export const evalProgram = (program: Program): Result<Value> =>
    evalSequence(program.exps, theGlobalEnv);

export const evalParse = (s: string): Result<Value> =>
    bind(p(s), (x) =>
            bind(parseL4Exp(x), (exp: Exp) =>
                evalSequence([exp], theGlobalEnv)));

// LET: Direct evaluation rule without syntax expansion
// compute the values, extend the env, eval the body.
const evalLet = (exp: LetExp, env: Env): Result<Value> => {
    const vals = mapResult((v: CExp) => applicativeEval(v, env), map((b: Binding) => b.val, exp.bindings));
    const vars = map((b: Binding) => b.var.var, exp.bindings);
    return bind(vals, (vals: Value[]) => evalSequence(exp.body, makeExtEnv(vars, vals, env)));
}

// @@ L4-EVAL-BOX 
// LETREC: Direct evaluation rule without syntax expansion
// 1. extend the env with vars initialized to void (temporary value)
// 2. compute the vals in the new extended env
// 3. update the bindings of the vars to the computed vals
// 4. compute body in extended env
const evalLetrec = (exp: LetrecExp, env: Env): Result<Value> => {
    const vars = map((b: Binding) => b.var.var, exp.bindings);
    const vals = map((b: Binding) => b.val, exp.bindings);
    const extEnv = makeExtEnv(vars, repeat(undefined, vars.length), env);
    // @@ Compute the vals in the extended env
    const cvalsResult = mapResult((v: CExp) => applicativeEval(v, extEnv), vals);
    const result = mapv(cvalsResult, (cvals: Value[]) => 
                        zipWith((bdg, cval) => setFBinding(bdg, cval), extEnv.frame.fbindings, cvals));
    return bind(result, _ => evalSequence(exp.body, extEnv));
};

// L4-eval-box: Handling of mutation with set!
const evalSet = (exp: SetExp, env: Env): Result<void> =>
    bind(applicativeEval(exp.val, env), (val: Value) =>
        mapv(applyEnvBdg(env, exp.var.var), (bdg: FBinding) =>
            setFBinding(bdg, val)));

