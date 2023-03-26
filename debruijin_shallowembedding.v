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
Notation "# x" := (UnitP x) (at level 58, right associativity).
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
Example ep3 : eProp := AbsP (#0). (* lambda x.x *)
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

Inductive ePropDB :=
  | TrueDB : ePropDB
  | FalseDB : ePropDB
  | UnitDB : nat -> ePropDB
  | InjDB : ePropDB -> ePropDB -> ePropDB (*OR*)
  | ConjDB : ePropDB -> ePropDB -> ePropDB (*AND*)
  | ImpDB : ePropDB -> ePropDB -> ePropDB
  | NegDB : ePropDB -> ePropDB
  | AbsDB : ePropDB -> ePropDB
  | AppDB : ePropDB -> ePropDB -> ePropDB
  .

(* Notation envDB := (list (nat * string)). *)
Notation envDB := (list nat).

(* Suppose the edge case never happens... *)

Fixpoint lookup (n : nat) (l : envDB) : nat :=
  match l with
  | nil => 0
  | x :: xs => if n =? x then 0 else S (lookup n xs)
  end.

Fixpoint interpX (p : eProp) (env : envDB) : ePropDB :=
  match p with
  | TrueP => TrueDB
  | FalseP => FalseDB
  | UnitP n => UnitDB (lookup n env)
  | InjP n1 n2 => InjDB (interpX n1 env) (interpX n2 env)
  | ConjP n1 n2 => ConjDB (interpX n1 env) (interpX n2 env)
  | ImpP n1 n2 => ImpDB (interpX n1 env) (interpX n2 env)
  | NegP n => NegDB (interpX n env)
  | AbsP p => AbsDB (interpX p (0 :: map S env))
  | AppP p1 p2 => AppDB (interpX p1 env) (interpX p2 env)
  end.

Notation "[[ p ]]" := (interpX p nil).
Notation "[[ p | env ]]" := (interpX p env).

Example interp_1 : ePropDB := [[ AbsP (#0) ]].
Compute interp_1.
Example interp_2 : ePropDB := [[ AbsP (AbsP (#0)) ]].
Compute interp_2.
Example interp_3 : ePropDB := [[ AppP (AbsP (AppP (#0) (#0))) (AbsP (AppP (#0) (#0))) ]].
Compute interp_3.
(* NOTE: if the env is nil, the number being returned will be directly cut down to 0. Hence 
the interpreted number appears to be 1.
The thing here could be that, even in the original language the abstraction is still somehow
fuzzy. We don't know what is x, what is y and what does the unit number means. Or maybe it
actually saved some efforts. *)
Example interp_4 : ePropDB := [[ AppP (AbsP (AppP (#10) (#10))) (AbsP (AppP (#10) (#10))) ]].
Compute interp_4.

(* STUB *)
Fixpoint substX (p : ePropDB) (env : list eProp) : ePropDB :=
  match p with
  | _ => UnitDB 100
  end.

(* STUB *)
Fixpoint evalX (p : ePropDB) (env : list eProp) : ePropDB :=
  match p with
  | _ => UnitDB 100
  end.
 
(* **************************************** *)
(* 1ST ATTEMPT *)

(* Ideal case for deep interpretation:

#"x" /\ #"y" /\ #"z"
== interpret into =>
$0 /\ $1 /\ $2 <= with a "environment" == [($0, "x"), ($1, "y"), ($2, "z")]

TODO:
  if (find var in env)
  => interpret as var
  else => shift all vars and interpret as new var
*)

(* Definition string_eq (s1 s2 : string) : bool :=
  match string_dec s1 s2 with
  | left _ => true
  | right _ => false
  end.

Fixpoint findVar (s : string) (env : envDB) : bool :=
  match env with
  | nil => false
  | (_, s') :: es => 
    if string_eq s s' then true 
    else findVar s es
  end.

Fixpoint createVar (s : string) (env : envDB) : envDB. Admitted.

Fixpoint interp (p : eProp) (env : envDB) : (ePropDB, envDB) :=
  match p with
  | TrueP => (TrueDB, env)
  | FalseP => (FalseDB, env)
  (* TODO: change environment *)
  (* TODO: carefully calculate a variable's number? *)
  | UnitP s => if findVar s env then _ else ((UnitDB 0), env)
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
                  end *)

(* **************************************** *)
(* 2ND ATTEMPT *)
(* **************************************** *)

(* Fixpoint shift (d : nat) (c : nat) (f : eProp) : eProp :=
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

(* This interp translates and evaluates the proposition to a de bruijin term to the end 

   The interpretation is actually a big-step evaluation. Maybe I just need to merely 
 interpret it rather than evaluate it... *)
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
                       | AbsP t3 => interpX t3 ((interpX t2 ctx xx) :: (map (shift 1 0) ctx)) xx
                       | _ => AppP (interpX t1 ctx xx) (interpX t2 ctx xx)
                       end
        end
  end.

Definition interp (p : eProp) (ctx : context) : eProp := 
  interpX p ctx (countDepth p 1). *)

(* **************************************** *)

(* Notation "[[ p ]]" := (interp p nil).
Notation "[[ p | ctx ]]" := (interp p ctx).

Example interp_1 : eProp := [[ ep1 ]].
Example interp_2 : eProp := [[ ep4 | nil ]].
Example interp_3 : eProp := [[ ep5 | (AbsP (#0)) :: (AbsP (#0)) :: nil]].

(* ep5 := AppP (AbsP (#2)) (#0). *)
(* ctx1 :=  (AbsP (#0)) :: (AbsP (#0)) :: nil *)
(* ctx2 :=  (AbsP (#0)) :: (AbsP (#1)) :: nil *)
(* TODO: figure out why the result is different *)

(*
AppP (AbsP (#2)) (#0) | (AbsP (#0)) :: (AbsP (#0)) :: nil
= [(AbsP (#2)) | ctx]

AppP (AbsP (#2)) (#0) | (AbsP (#0)) :: (AbsP (#1)) :: nil

*)

Compute interp_1.
Compute interp_2.
Compute interp_3. *)

(************************************************)

Inductive asserted : ePropDB -> Prop := 
  | Asserted : forall (e: ePropDB), asserted e.

Definition extract (p : Prop) : ePropDB :=
  match p with
  | Asserted _ => UnitDB 100
  | _ => UnitDB 100
  end.

Notation Pp := (asserted).

Definition pp1_1 (e : eProp) : Prop := Pp [[ e ]].
(*
asserted nil e : Prop :=
Asserted : forall (c : context)

*)

Definition pp1_11 := forall (e1 e2: eProp),
  asserted [[ e1 ]]
  -> asserted [[ e1 =) e2 ]]
  -> asserted [[ e2 ]].

Definition pp1_2 := forall p: eProp, Pp [[ (p \/ p) =) p ]].

Definition pp1_3 := forall p q: eProp, Pp [[ q =) (p \/ q) ]].

Definition pp1_4 := forall p q: eProp, Pp [[ (p \/ q) =) (q \/ p) ]].

Definition pp1_5 := forall p q r: eProp, Pp [[ (p \/ (q \/ r)) =) (q \/ (p \/ r)) ]].

Definition pp1_6 := forall p q r: eProp, Pp [[ (q \/ r) =) (p \/ q) =) (p \/ r) ]].

(* Theorem pp1_7: Pp (If p is a eProp, then --p is a eProp). *)

(* Theorem pp1_71: Pp (If p, q are eProps, then p \/ q is a eProp). *)

(* Theorem pp1_72: Pp (If p, q are elemental functions, then p(x) \/ q(x) is a elemental function). *)

Require Import Coq.Program.Equality.

Theorem n2_01 : forall p: eProp, Pp [[ (p =) (--p)) =) (--p) ]].
Proof.
  intros.
  pose (fun x =>[[ x ]]) as new_prop_r.
  pose (new_prop_r (--p)) as new_prop.
  change (new_prop_r (--p)) with ([[ --p ]]) in new_prop.
  clear new_prop_r.
  pose (Pp new_prop) as new_prop_pp.
  change (Pp new_prop) with (Pp [[ --p ]]) in new_prop_pp.
  destruct new_prop_pp as [e].

(* TODO:
I should find a way to present something like this:

I can use Taut with --p substitute for p as a proposition.
This proposition serves as a "Antecedent".
With this proposition we can arrive at the latter proof.

I need to make sure the interpretation does not go wrong in advance.
*)
Admitted.


End PM.
