

From Stdlib Require Export Program.Equality.
From TestingTheory Require Export Must VACCS_Good gLts InteractionBetweenLts ActTau.
Include VACCS_Testing.




 





























(* Tactic that looks for lts/lts_step assumptions and inverts them to
  learn about the shape of the conclusion *)
(*
Ltac lts_inversion :=
try match goal with
| H : lts_step ?p ?a ?q |- _ =>
  solve[inversion H; subst; discriminate || tauto]
| H : lts ?p ?a ?q |- _ => inversion H; subst; discriminate || tauto
 end;
match goal with
| H : lts_step ?p ?a ?q |- _ => inversion H; subst; clear H
| H : lts ?p ?a ?q |- _ => inversion H; subst; clear H
 end.
*)





(*========= notations =====================*)
Notation "p ⊑ q" := (ctx_pre p q) (at level 40).

Notation tau q := (g (𝛕 • q)).
Notation out x v := (x ! v • 𝟘).
Notation inp x p := (g (x ? p)).
Notation sum p q := (g (p+q)).
Notation gsum p q := (p+q).
Notation gtau p  := (gpr_tau p).
Notation ginp x p := (gpr_input x p).





Notation Linp c v :=  ( ActTau.ActExt (InputOutputActions.ActIn (c ⋉ v)) ).
Notation Lout c v := ( ActTau.ActExt (InputOutputActions.ActOut (c ⋉ v))  ).
Notation Ltau := ActTau.τ.


Notation sub t1 x1 := (t1 ^ x1).
Notation congs := cgr.



(*=========== cong preseves mp ===============*)
Lemma mp_congsL: forall p e r: proc,
  p must_pass e -> congs p r ->  r must_pass e .
Proof.
intros. 
set (lem:= must_eq_server p r e).
specialize (lem H0); auto.
Qed. 

Lemma mp_congsR: forall p e r: proc,
  p must_pass e -> congs e r ->  p must_pass r.
Proof.
intros. 
set (lem:= must_eq_client p e r).
specialize (lem H0); auto.
Qed. 
(*========== other cong and << stuff  ============*)




Lemma mpless_congs: forall p q r: proc,
  ( p ⊑ q) -> (congs q r) ->  
    (p ⊑ r).
Proof.
unfold "⊑"; intros.
specialize (H _ H1).
set (lem:= mp_congsL _ _ _ H H0); auto.
Qed.

Proposition mpless_trans: forall p q r:proc,
  p ⊑ q ->   q ⊑ r ->  
    p ⊑ r.
Proof.
unfold "⊑"; auto.
Qed.



Hint Constructors lts :mdb.
