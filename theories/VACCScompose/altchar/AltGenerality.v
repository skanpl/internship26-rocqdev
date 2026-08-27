
From Stdlib Require Export Program.Equality .
From stdpp Require Export gmap.
From TestingTheory Require Export Must VACCS_Good gLts InteractionBetweenLts ActTau.
Include VACCS_Testing.


From TestingTheory Require Export DefinitionAS Convergence Termination.

Require Export List.
Require Export stdpp.base.
 

Require Export ForwarderConstruction.



(*---------------- notations -------------------------*)
Notation wt := WeakTransitions.wt.
Notation tau p := (g (𝛕 • p)).  
Notation inp x p := (g (gpr_input x p)).
Notation gtau p := (gpr_tau p).
Notation out c v := (c ! v • 𝟘).
Notation sum p q := (g (gpr_choice p q)).



Notation Linp c v :=  ( ActTau.ActExt (InputOutputActions.ActIn (c ⋉ v)) ).
Notation Lout c v := ( ActTau.ActExt (InputOutputActions.ActOut (c ⋉ v))  ).
Notation Ltau := ActTau.τ.
Notation sub t1 x1 :=  (subst_in_proc 0 x1 t1).


Notation ash mu :=  (VarC_action_add 1 mu). (*ash=action shift*)
Notation alpha := (𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ). (*abstraction on a mu*)
Notation Alpha := (Subset_Act.map_set alpha). (*abstraction on a set of mus*)


Notation Aout c v := (InputOutputActions.ActOut (c ⋉ v)).
Notation Ainp c v := (InputOutputActions.ActIn (c ⋉ v)).
Notation vact := (InputOutputActions.ExtAct TypeOfActions).
(*------------------- misc -----------------------------------*)

Hint Constructors lts :mdb.


Lemma delta_id: forall pmu,
  𝝳ᴠᴀᴄᴄꜱ pmu = pmu.
Proof.
intro; destruct pmu,c; cbv; auto.
Qed.


Lemma inv_mu: forall mu,
  exists x v, ( ActExt mu = Linp x v) \/  
              (ActExt mu = Lout x v)   .
Proof.
intros; destruct mu,a; eauto.
Qed.



Lemma mu_impl_wt: forall p q mu, lts p (ActExt mu) q ->  
  wt p [mu] q.
Proof.
intros ? ? ? Hp.  
eapply WeakTransitions.wt_act; eauto with mdb.
Qed.




Lemma ltau_dec: forall p,
  (exists p', lts p Ltau p') \/ 
  (forall p', lts p Ltau p' -> False).
Proof.
intros; set (decp:= proc_stable_dec p Ltau); 
destruct decp as [decp| decp];
unfold proc_stable in decp; cbn in decp.
- right; intros ? H; set (lem:= lts_set_tau_spec1 _ _ H); set_solver.
- left; set (empdec:= set_choose_or_empty (lts_set_tau p)).
  destruct empdec as [empdec|empdec]; try set_solver.
  set (lem:= lts_set_tau_spec0); set_solver.
Qed.

(*------------ ref -----------------------*)
Lemma ref_exf: forall p p', 
  p ↛ -> lts p Ltau p' -> False.
Proof.
intros; inversion H.
eapply lts_set_tau_spec1 in H0; set_solver.
Qed.

Lemma ref_exf_rev: forall p , 
  (forall p', lts p Ltau p' -> False) -> p ↛.
Proof.
intros ? H. 
unfold "↛"; cbn; unfold proc_stable; cbn.
set (empdec:= set_choose_or_empty (lts_set_tau p)).
destruct empdec; try destruct H0; try set_solver.
set (lem:= lts_set_tau_spec0 _ _ H0).
exfalso; eauto using H. 
Qed.
(*--------------- double negation elimination ------------------*)


Lemma inv_nonmublock: forall p mu,
  (¬ (p ↛[mu])) -> exists q,  
  lts p (ActExt mu) q  \/ lts p (ActExt mu) q.
Proof.
intros ? ? Hnmb.
simpl in Hnmb.
unfold proc_stable, lts_set in *.
destruct (inv_mu mu) as [x [v H]].
destruct H as [H|H]; inversion H; subst; eauto.
- set (empdec:=  set_choose_or_empty (lts_set_input p (x ⋉ v))) .
  destruct empdec as [empdec|empdec].
  * destruct empdec as [q empdec]. set (lem:= lts_set_input_spec0 _ _ _ empdec).
     repeat eexists; eauto.
  * set_solver.
- set (empdec:=  set_choose_or_empty (lts_set_output p (x ⋉ v))) .
  destruct empdec as [empdec|empdec].
  * destruct empdec as [q empdec]. set (lem:= lts_set_output_spec0 _ _ _ empdec).
     repeat eexists; eauto.
  * set_solver.
Qed.

Lemma inv_nonmublock_rev: forall p mu,
  (exists q, lts p (ActExt mu) q)  -> (¬ (p ↛[mu]))  .
Proof.
intros ? ? H. 
destruct H as [q Hlt].
intro.
set (lem := inv_mu mu).
destruct lem as [x [v [Hmueq|Hmueq]]]; inversion Hmueq; subst.
- eapply lts_set_input_spec1 in Hlt; set_solver.
- eapply lts_set_output_spec1 in Hlt; set_solver.
Qed.


Lemma inv_nonblock_rev: forall p,
  (exists q, lts p Ltau q)  -> ¬ (p ↛)  .
Proof.
intros ? H0 H. 
destruct H0 as [q Hlt].
eapply lts_set_tau_spec1 in Hlt; set_solver.
Qed.

(*---- extention to stable lemmas (maybe useless bcs already proven) --------*)

Lemma extend_to_stable: forall p,
  p⤓ -> exists p', 
  wt p [] p' /\  (forall q, lts p' Ltau q -> False).  
Proof.
intros ? Hter.
dependent induction Hter.
set (decp:= proc_stable_dec p Ltau).
destruct decp as [decp| decp];
unfold proc_stable in decp; cbn in decp.
- exists p; split; eauto with mdb.
  intros p' Hlt. 
  set (lem:= lts_set_tau_spec1 _ _ Hlt).
  set_solver.
- set (empdec:= set_choose_or_empty (lts_set_tau p)).
  destruct empdec as [empdec|empdec]; try set_solver.
  destruct empdec as [p' Hlt].
  apply lts_set_tau_spec0 in Hlt.
  specialize (H0 _ Hlt). 
  destruct H0 as [q [Hwt Href]].
  eauto with mdb.
Qed.


Lemma extend_to_stable_trace: forall p p0 s,
  p⇓s -> wt p s p0 -> exists p', 
  wt p s p' /\  (forall q, lts p' Ltau q -> False).  
Proof.
intros ? ? ? Hcnv.
dependent induction Hcnv; eauto using extend_to_stable. 
intro Hwt; replace (μ :: s) with ([μ]++s) in Hwt; auto.
apply WeakTransitions.wt_split in Hwt.
destruct Hwt as [q [Hp Hq]].
specialize (H1 _ Hp Hq); destruct H1 as [p' [Hq2 Href]].
set (lem:= WeakTransitions.wt_concat _ _ _ _ _ Hp Hq2); 
eauto.
Qed.


