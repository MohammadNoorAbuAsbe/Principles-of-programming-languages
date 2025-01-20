import { Result, makeFailure, makeOk, bind, either, isOk } from "../lib/result";
/* Library code */
const findOrThrow = <T>(pred: (x: T) => boolean, a: T[]): T => {
    for (let i = 0; i < a.length; i++) {
        if (pred(a[i])) return a[i];
    }
    throw "No element found.";
}

const ff:<T>(pred: (x: T) => boolean , a: T[]) => T[] = <T>(pred: (x: T) => boolean ,a: T[]): T[] => a.filter((a: T) => pred(a));
const filterA:<T>(t:T[]) => Result<T> = <T>(t: T[]):Result<T> => t.length > 0 ? makeOk(t[0]) : makeFailure("there is no such element in the array that matches the condition");

export const findResult = <T>(pred: (x: T) => boolean, a: T[]): Result<T> => filterA(ff(pred,a));


/* Client code */
const returnSquaredIfFoundEven_v1 = (a: number[]): number => {
    try {
        const x = findOrThrow(x => x % 2 === 0, a);
        return x * x;
    } catch (e) {
        return -1;
    }
}
export const returnSquaredIfFoundEven_v2 = (a: number[]): Result<number> => {
    const x = findResult(x => x % 2 === 0, a);
    return bind(x,x => makeOk(x * x));
}

export const returnSquaredIfFoundEven_v3 = (a: number[]): number => {
    const x = findResult(x => x % 2 === 0, a);
    return either(x,x => x * x,x => -1);
}