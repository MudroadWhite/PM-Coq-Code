# Notes

##### PL.v

`PL.v` is the current initial complete attempt to formalize chatper 1-5 of PM's propositions. Right after chapter 5 of PM we're going to do chapter 9 of PM. The problem in translating the propositions and proofs here happens with the proposition 9.2. The problem here seems to be that Coq can recognize function and automatically apply the terms for propositions without quantifiers, but when a proposition with quantifier appears, Coq fails to treat it properly. 

(**Problem to be stated here more clearly for future reference**)

To solve this issue, Landon suggests that I should make a De Bruijin shallow embedding on PM. Some initial difficulties are being met, such as "What is a shallow embedding?" "How do I write a shallow embedding?" and these problems are partially resolved with ChatGPT.

##### debruijin_shallowembedding.v

`debruijin_shallowembedding.v` is the current work on shallow embedding of PM. The core to the shallow embedding is defining a interpretation function to interpret the original language into a De Bruijin Index representation of the original language. The first attempt to define this `interp` function has met several problems and they are resolved with [Reddit](https://www.reddit.com/r/Coq/comments/11mlu81/cannot_determine_decreasing_argument_for_fix/). With these issue resolved, I can arrive at more details to see what should be modified and what I have ignored. 

Several problems arrives: 1. Is `interp` actually working as I wished? This happens when I use some cases to test this function. 2. How should you record the propositions in PM with the interp function? 3. What does it mean to derive(|-) in this sense? 4. What is the context for derive? It seems different from the "context" of `interp`. Here should be with a renaming issue.

(To be updated)