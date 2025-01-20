
import * as R from "ramda";

const stringToArray = R.split("");

const lowercase :(str: string) => string = (str: string) => str.toLowerCase();
const lowercaseTheArray = R.map(lowercase);

const final = function (acc: {[index:string]: never | number}, curr:string) {
  return acc[curr] ? ++acc[curr] : acc[curr] = 1, acc
};

const checkForSpaces:(s:string) => boolean = (s: string):boolean => s !== " ";
  export const countLetters: (s: string) => {} = (s: string): {} =>
  R.pipe(
      stringToArray,
      R.filter(checkForSpaces),
      lowercaseTheArray,
      R.reduce(final, {})
      )(s);



/* Question 2 */

const closers = ["}", "]", ")"] as const;
type Closers = (typeof closers)[number];
const isCloser = (x: any): x is Closers => closers.includes(x);

const openers = ["{", "[", "("] as const;
type Openers = (typeof openers)[number];
const isOpener = (x: any): x is Openers => openers.includes(x);

const closersANDopeners = ["(", "[", "{", "}", "]", ")"] as const;
type ClosersAndOpeners = (typeof closersANDopeners)[number];
const isClosersAndOpeners = (x: any): x is ClosersAndOpeners => closersANDopeners.includes(x);
const closerToOpener:(s:string) => string = (s:string):string=>
  s === ")" ? "(" : s === "}" ? "{" : s === "]" ? "[" : "0";

const checkPairs:(s:string[], s2:string)=> string[] = (s:string[], s2:string) : string[] =>
  isOpener(s2) ? R.concat(s,[s2]): s[s.length - 1] === closerToOpener(s2)? R.slice(0,s.length -1 , s): R.concat(s,["notPaired"]);

export const isPaired: (s: string) => boolean = R.pipe(
  stringToArray,
  R.filter(isClosersAndOpeners),
  R.reduce(checkPairs,[]),
  R.isEmpty
)


/* Question 3 */
export interface WordTree {
    root: string;
    children: WordTree[];
}

const recc:(t: WordTree) => string[] = (t:WordTree): string[] =>  
t.children.length === 0? [t.root]: [t.root].concat(R.map(recc, t.children).reduce((acc:string[], curr:string[]) => acc.concat(curr), []));

const union:(s:string[]) => string = (s : string[]) : string => s.join(" ");
  
export const treeToSentence : (t: WordTree)=> string = R.pipe(recc, union);