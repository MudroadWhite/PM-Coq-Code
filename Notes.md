# Notes

This Markdown files serves as a document for notes on writing each of the Coq files when developing the formalization for PM. It is expected that I can take serious note here describing the issues I occur for future reference, or already resolved problems.

## PL.v

`PL.v` is the current initial complete attempt to formalize chatper 1-5 of PM's propositions. Right after chapter 5 of PM we're going to do chapter 9 of PM. The problem in translating the propositions and proofs here happens with the proposition 9.2. The problem here seems to be that Coq can recognize function and automatically apply the terms for propositions without quantifiers, but when a proposition with quantifier appears, Coq fails to treat it properly. 

This can be seen particularly in the following snippet:

``` Coq
Theorem n9_21 : forall (Phi Psi : Prop -> Prop),
  (forall x, Phi x -> Psi x) -> (forall x, Phi x) -> (forall x, Psi x).
Proof. intros Phi Psi z.
  (** S1 **)
  specialize Id2_08 with (forall z: Prop, Psi z -> Psi z). intros Id2_08a.
  (** S2 **)
  specialize n9_1 with (Phi y). intro n9_1a.
Admitted.
```

Now let's look back to the original proof on PM. Using modern logical connectives it can be written like this:

```
*9.21. |- (Ax.p(x) -> q(x)) -> (Ax.p(x)) -> Ax.q(x)
Proof. (*The brackets for predicates will be ignored for brevity*)
(*1)	|- *2.08 			-> |- (pz -> qz) -> (pz -> qz) 
(*2)	|- (1).*9.1			-> |- Ey.(pz -> qz) -> (py -> qz)
(3)		|- (2).*9.1			-> |- Ex.Ey.(px -> qx) -> (py -> qz)
(4)		|- (3).*9.13		-> |- Az.Ex.Ey.(px -> qx) -> (py -> qz)
(5)		[(4).*9.06]			|- Az.(Ex.px -> qx) -> (Ey.py -> qz)
(6)		[(5).(*1.01.*9.08)]	|- (Ex.~(px -> qx)) \/ Az.Ey.(~py \/ qz)
(7) 	[(6).(*9.08)]		|- (Ex.~(px -> qx)) \/ Ey.(~py \/ Az.qz)
(8) 	[(7).(*1.01)]		|- (Ax.px -> qx) -> (Ay.py) -> Az.qz
```

### Problem 1: Inconsistent Proof Style

Let's look at the two lines with stars. We can see that we can indeed introduce `forall z: Prop, Psi z -> Psi z` into the context and match the `(1)` in the original proof. But let's take a look at what would happen for `(2)`. `Id2_08` is defined as `∀ P : Prop,  P → P.`  

Principia Mathematica presents its proof in forward steps, while Coq likes to proof stuffs, as proof trees, from roots to the leaves and keep transforming the proof goals. Now, we want to introduce a new variable `y` into the context, without disturbing the way that PM goes on its proof. But it seems like impossible to give the new variable using backward steps in Coq. So we should build a language to translate the proof. Otherwise, if we go on with `  specialize n9_1 with (Phi y)`, Coq will report that 

```
The reference y was not found in the current environment.
```

### Problem 2: Bad Proposition Type

Another problem is the type for the propositions and variables. (**TODO: to be explained here in detail for future reference**)

To solve this issue, Landon suggests that I should make a De Bruijin shallow embedding on PM. Some initial difficulties are being met, such as "What is a shallow embedding?" "How do I write a shallow embedding?" and these problems are partially resolved with ChatGPT.

## debruijin_shallowembedding.v

`debruijin_shallowembedding.v` is the current work on shallow embedding of PM. The core to the shallow embedding is defining a interpretation function to interpret the original language into a De Bruijin Index representation of the original language. The first attempt to define this `interp` function has met several problems and they are resolved with [Reddit](https://www.reddit.com/r/Coq/comments/11mlu81/cannot_determine_decreasing_argument_for_fix/). With these issue resolved, I can arrive at more details to see what should be modified and what I have ignored. 

Several problems arrives: 1. Is `interp` actually working as I wished? This happens when I use some cases to test this function. 2. How should you record the propositions in PM with the interp function? 3. What does it mean to derive(|-) in this sense? 4. What is the context for derive? It seems different from the "context" of `interp`. Here should be with a renaming issue.

### Problem 1: Weird `context` Error

The first problem that should arrive however is when I record this proposition:

```coq
Definition pp1_11 (p : eProp) : Prop := forall (e1 e2: eProp),
  asserted [[ e1 ]]
  -> asserted [[ e1 =) e2 ]]
  -> asserted [[ e2 ]].
```

For the `asserted [[ e1 ]]` the Coq will report

```
In environment
p : eProp
e1 : eProp
e2 : eProp
The term "[[e1]]" has type "eProp" while it is expected to have type "context".
```

And I still don't know what it means.

### Problem 2: Compatibility with Forward Proof

With the power of `interp`, proposition should be recorded in a style like follows:

```Coq
Theorem x : forall (x y z : eProp), asserted [[ P(x, y, z) ]] (* For some proposition P *).
```

Referring back to [Inconsistent Proof Style](###Problem 1:\ Inconsistent Proof Style) issue in `PL.v`, we somehow wish to see we can introduce a new variable as we like during the proof procedure. Does it really work out for this interpretation? Can it present a new variable as needed?... For now, it seems to be ok.

**(BELOW IS DRAFT)**

### Problem X: Judgement-scale representation

The specification still misses some stuffs that appeared in the proof:

- Do I need to concern about judgements like `A|-B`? Then it's definitely different from the so-called `context`.