Require Import String.
Require Import List.
Require Import Arith.
Require Import Nat.

Module PM.

Example x : string := "12345".

Inductive eProp :=
  | TrueP : eProp
  | FalseP : eProp
  | UnitP : nat -> eProp
  | InjP : eProp -> eProp -> eProp (*OR*)
  | ConjP : eProp -> eProp -> eProp (*AND*)
  | ImpP : eProp -> eProp -> eProp
  | NegP : eProp -> eProp
  | AbsP : eProp -> eProp
  | AppP : eProp -> eProp -> eProp
  .

(* The level is slightly lower than the level for list operator :: . *)
Notation "# x" := (UnitP x) (at level 59, right associativity).
Notation "x \/ y" := (InjP x y).
Notation "x /\ y" := (ConjP x y).
Notation "-- x" := (NegP x) (at level 59, right associativity).
Notation "x =) y" := (ImpP x y) (at level 59, right associativity).

(* Inductive eFunc := (* Only takes one argument *)
  | EFunc : string -> eProp -> eFunc. *)

Example ep1 : eProp := (# 0) \/ (# 1).
Print ep1.
Example ep2 : eProp := -- (#0 /\ #1).
Print ep2.
Example ep3 : eProp := AbsP (# 0). (* lambda x.x *)
Print ep3.
Example ep4 := AbsP (#0).
Example ep5 := AppP (AbsP (#2)) (#0).

(* Inductive context := 
  | None : context
  | Some : eProp -> context -> context. *)


(* The context here is for de bruijin interpretaton, or actually the environment. 
  How about the context for deduction? *)
Notation context := (list eProp).

Example ctx_two_vars : context := #0 :: #1 :: nil.
Print ctx_two_vars.

(************************************************)
(* De Bruijin Index Interpretation *)

(* Inductive deBruijin :=
  | L : deBruijin -> deBruijin (* Abstraction *)
  | A : deBruijin -> deBruijin (* Appllication *)
  | N : nat -> deBruijin (* Index *)
  . *)

Fixpoint shift (d : nat) (c : nat) (f : eProp) : eProp :=
  match f with
  | UnitP n =>
      if leb c n then UnitP (d + n) else UnitP n
  | TrueP => TrueP
  | FalseP => FalseP
  | InjP n1 n2 => InjP (shift d c n1) (shift d c n2)
  | ConjP n1 n2 => ConjP (shift d c n1) (shift d c n2)
  | ImpP n1 n2 => ImpP (shift d c n1) (shift d c n2)
  | AbsP n1 =>
      AbsP (shift d (c+1) n1)
  | AppP n1 n2 =>
      AppP (shift d c n1) (shift d c n2)
  | NegP n => NegP (shift d c n)
  end.

Fixpoint countDepth (p : eProp) (n : nat) : nat :=
  match p with 
  | UnitP _ => n+1
  | TrueP => n+1
  | FalseP => n+1
  | InjP p1 p2 => max (countDepth p1 n) (countDepth p2 n) + 1
  | ConjP p1 p2 => max (countDepth p1 n) (countDepth p2 n) + 1
  | ImpP p1 p2 => max (countDepth p1 n) (countDepth p2 n) + 1
  | AbsP _ => n+1
  | AppP p1 p2 => max (countDepth p1 n) (countDepth p2 n) + 1
  | NegP _ => n+1
  end.

Fixpoint interpX (p : eProp) (ctx : context) (x : nat) {struct x} : eProp :=
  match x with
  | 0 => FalseP
  | S xx => match p with
        | TrueP => TrueP
        | FalseP => FalseP
        | UnitP n => nth n ctx (UnitP n)
        | InjP n1 n2 => match interpX n1 ctx xx, interpX n2 ctx xx with
                        | FalseP, FalseP => FalseP
                        | _, _ => TrueP
                        end
        | ConjP n1 n2 => match interpX n1 ctx xx, interpX n2 ctx xx with
                        | TrueP, TrueP => TrueP
                        | _, _ => FalseP
                        end
        | ImpP n1 n2 => match interpX n1 ctx xx, interpX n2 ctx xx with
                        | FalseP, _ => TrueP
                        | TrueP, TrueP => TrueP
                        | _, _ => FalseP
                        end
        | NegP n => match interpX n ctx xx with
                        | TrueP => FalseP
                        | _ => TrueP
                        end
        (* Append a variable to environment and add 1 index to all other values *)
        | AbsP t1 => AbsP (interpX t1 (UnitP 0 :: map (shift 1 0) ctx) xx)
        | AppP t1 t2 => match interpX t1 ctx xx with
                       (* Problem: Cannot guess decreasing argument of fix *)
                       | AbsP t3 => interpX t3 ((interpX t2 ctx xx) :: (map (shift 1 0) ctx)) xx
                       | _ => AppP (interpX t1 ctx xx) (interpX t2 ctx xx)
                       end
        end
  end.

Definition interp (p : eProp) (ctx : context) : eProp := 
  interpX p ctx (countDepth p 1).

Notation "[[ p ]]" := (interp p nil).
Notation "[[ p | ctx ]]" := (interp p ctx).

Example interp_1 : eProp := [[ ep1 ]].
Example interp_2 : eProp := [[ ep4 | nil ]].
Example interp_3 : eProp := [[ ep5 | (AbsP (#0)) :: (AbsP (#0)) :: nil]].

(* ep5 := AppP (AbsP (#2)) (#0). *)
(* ctx1 :=  (AbsP (#0)) :: (AbsP (#0)) :: nil *)
(* ctx2 :=  (AbsP (#0)) :: (AbsP (#1)) :: nil *)
(* TODO: figure out why the result is different *)

Compute interp_1.
Compute interp_2.
Compute interp_3.

(************************************************)

Inductive asserted : context -> eProp -> Prop := 
  | Asserted : forall (c : context) (e : eProp), asserted c e.

Notation Pp := (asserted nil).

Definition pp1_1 (p : eProp) : Prop := Pp (#0).

Definition pp1_11 (p : eProp) : Prop := forall (c1 c12: context) (e1 e2: eProp),
  asserted c1 e1
  -> asserted c12 (ImpP e1 e2)
  -> asserted (append_ctx c1 c12) e2.

Definition pp1_2 := forall p: eProp, 
  Pp (ImpP (p /\ p) p).

Definition pp1_3 := forall p q: eProp,
  Pp (ImpP q (InjP p q)).

Definition pp1_4 := forall p q: eProp,
  Pp (ImpP (InjP p q) (InjP q p)).

Definition pp1_5 := forall p q r: eProp,
  Pp (ImpP (InjP p (InjP q r)) (InjP q (InjP p r))).

(* Definition pp1_6 := forall p q r: eProp,
  Pp ()
 *)



End PM.
