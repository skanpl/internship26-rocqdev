 

Require Import CtxGenerality.











(*================= tau ==============================*)
Proposition ctx_compose_tau: forall p q, p ⊑ q -> 
  tau p ⊑ tau q.
Proof.
unfold ctx_pre.
intros p q Hmust e Hfoc.
dependent induction Hfoc; eauto with mdb.
destruct ex as [r trans].
inversion trans;subst.
- inversion l. subst.
  apply m_step; eauto with mdb.
  * eexists. do 2 constructor.
  * intros p' Hq. inversion Hq; subst; eauto with mdb. 
  * intros. inversion H3; eauto with mdb.
- eapply m_step; eauto with mdb.
  * eexists. do 2 constructor.
  * intros p' Hq. inversion Hq; subst.
    assert (p must_pass t). eapply pt.  constructor.
    eapply Hmust. auto. 
  * intros; inversion H3.
- inversion l1. 
Qed.

(*================ input ==========================*)

Proposition ctx_compose_inp: forall c p q,
  (forall v, sub p v ⊑ sub q v) ->
  inp c p  ⊑ inp c q.
Proof. 
unfold ctx_pre.
intros c p q Hmust e Hfoc.
dependent induction Hfoc; eauto with mdb.
destruct ex as [r trans].
inversion trans;subst.
- inversion l.
- eapply m_step; eauto with mdb.
  * eexists. eapply ParRight. apply l.
  * intros p' Hq. inversion Hq.
  * intros p' e' μ1 μ2 Hpi Hq He.
    inversion Hq. subst.
    specialize (com (sub p v) e' _ μ2 Hpi) .
    apply Hmust.
    eapply com; [constructor | auto].
- inversion l1; subst. destruct μ2 as [|c']; inversion eq. subst c'.
  eapply m_step; eauto with mdb.
  * exists (sub q v, b2). eapply ParSync. eauto. constructor. auto.
  * intros. inversion H2.
  * intros q' e' μ1 μ0 Hpi Hq He.
    clear H pt et H0.
    inversion Hq; subst. destruct μ0 as [|c']; inversion Hpi. subst c'.
    clear eq. apply Hmust. eapply com; eauto. constructor.
Qed.

(*================ isum =================================*)

Definition isum (p q: proc) :=  g ((gpr_tau p) + (gpr_tau q)).

Lemma mp_tau: forall (p e: proc),
  p must_pass e ->  tau p must_pass e.
Proof.
intros p e Hmust.
induction Hmust; eauto with mdb.
eapply m_step; eauto with mdb.
- eexists; do 2 constructor.
- intros p' Htau; inversion Htau; subst; eauto with mdb.
- intros ? ? ? ? ? Htau; inversion Htau.
Qed.


Lemma mp_sum: forall (p q: gproc) (e:proc),
  (g p) must_pass e -> (g q) must_pass e -> 
  (sum p q) must_pass e.
Proof.
intros p q e Hmpp.
dependent induction Hmpp; intros; eauto with mdb.
eapply m_step; eauto with mdb.
- destruct ex as [r trans]; inversion trans; subst; eexists.
  * do 2 constructor; eauto.
  * eapply ParRight; eauto.
  * eapply ParSync; try constructor; eauto.
- intros P Hpq.
  inversion Hpq; subst.
  * apply pt; auto.
  * inversion H2; eauto with mdb.
- intros E He.
  apply H0; eauto. 
  inversion H2; eauto with mdb.
  exfalso; auto. 
- intros P E ? ? Hpi Hpq He.
  inversion Hpq; subst.
  * eapply com; eauto with mdb.
  * inversion H2; eauto with mdb.
    exfalso; auto. 
Qed.



Lemma mp_isum: forall (p q e: proc),
  p must_pass e -> q must_pass e -> 
  isum p q must_pass e.
Proof.
intros ? ? ? Hp Hq.
set (lemp:= mp_tau _ _ Hp).
set (lemq:= mp_tau _ _ Hq).
set (lemsum:= mp_sum _ _ _ lemp lemq).
auto.
Qed.



Lemma isuml: forall (p q:proc),  (isum p q)  ⟶  p.
Proof.
intros; unfold isum. 
constructor; eauto with mdb.
Qed.

Lemma isumr: forall (p q:proc),  (isum p q)  ⟶  q.
Proof.
intros; unfold isum. 
eapply lts_choiceR; eauto with mdb.
Qed.
 


Lemma mp_isum_rev: forall (p q e: proc),
 (isum p q) must_pass e -> 
 p must_pass e  /\ q must_pass e.
Proof.
intros ? ? ? Hisum.
dependent induction Hisum; eauto with mdb.
destruct ex as [r trans]; inversion trans; subst; 
try inversion l; subst; split; apply pt; eauto using isuml, isumr.
Qed.


Lemma isum_invert: forall (p q r: proc), (isum p q)  ⟶  r -> 
  r= p \/ r=q.
Proof.
intros ? ? ? Hisum.
inversion Hisum; subst; inversion H3; subst.
- left; auto.
- right; auto.
Qed.
 
Proposition ctx_compose_isum: forall (p1 p2 q:proc),
  p1 ⊑ p2  -> (isum p1 q) ⊑ (isum p2 q).
Proof.
unfold ctx_pre. 
intros ? ? ? Hmust ? Hfoc.
dependent induction Hfoc; eauto with mdb.
eapply m_step; eauto with mdb.
- eexists; constructor; eauto using isuml.
- intros P Hisum. set (invlem:= isum_invert _ _ _ Hisum).
  destruct invlem; subst; try eapply Hmust; eapply pt;
   eauto using isuml, isumr.
- intros ? ? ? ? ? Hisum; unfold isum in *; inversion Hisum; subst.
  inversion H7; subst. inversion H7.
Qed.
(*================== ifthenelse  =============================*)

(*---------   mp  to ifthenelse   --------------*)
Lemma mp_iftrue: forall (p q e: proc) E, 
  p must_pass e -> Eval_Eq E = Some true ->
  (If E Then p Else q) must_pass e.
Proof.
intros ? ? ? ? Hmp Hbool.
dependent induction Hmp; eauto with mdb.
eapply m_step; eauto with mdb.
- destruct ex as [r trans]; inversion trans; subst.
  * eexists; do 2 constructor; eauto.
  * eexists; eapply ParRight; eauto.
  * eexists; eapply ParSync; try constructor; eauto.
- intros P Hif.
  inversion Hif; subst; eauto with mdb.
  rewrite Hbool in *; inversion H7. 
- intros P e' ? ? Hpi Hif He.
  inversion Hif; subst; eauto with mdb.
  rewrite Hbool in *; inversion H7.
Qed.

Lemma mp_iffalse: forall (p q e: proc) E, 
  q must_pass e -> Eval_Eq E = Some false ->
  (If E Then p Else q) must_pass e.
Proof.
intros ? ? ? ? Hmp Hbool.
dependent induction Hmp; eauto with mdb.
eapply m_step; eauto with mdb.
- destruct ex as [r trans]; inversion trans; subst.
  * eexists; constructor; eapply lts_ifZero; eauto.
  * eexists; eapply ParRight; eauto.
  * eexists; eapply ParSync; try eapply lts_ifZero; eauto.
- intros P Hif.
  inversion Hif; subst; eauto with mdb.
  rewrite Hbool in *; inversion H7. 
- intros P e' ? ? Hpi Hif He.
  inversion Hif; subst; eauto with mdb.
  rewrite Hbool in *; inversion H7.
Qed.

(*-----------   mp from ifthenelse   -------------*)
Lemma mp_iftrue_rev: forall (p q e: proc) E, 
  Eval_Eq E = Some true -> (If E Then p Else q) must_pass e -> 
  p must_pass e.
Proof.
intros ? ? ? ? Hbool Hmp.
dependent induction Hmp; eauto with mdb.
eapply m_step; eauto with mdb.
- destruct ex as [r trans]; inversion trans; subst.
  * inversion l; subst; eexists; constructor; eauto.
    rewrite Hbool in *; inversion H7.
  * eexists; eapply ParRight; eauto.
  * eexists; eapply ParSync; eauto.
    inversion l1; subst; eauto.
    rewrite Hbool in *; inversion H7.
- clear H1 com et H0.
  intros ? Hp.
  eapply pt; constructor; eauto.
- intros ? ? ? ? Hpi Hp He.
  eapply com; try constructor; eauto.
Unshelve. apply (g 𝟘).
Qed. 


Lemma mp_iffalse_rev: forall (p q e: proc) E, 
  Eval_Eq E = Some false -> (If E Then p Else q) must_pass e -> 
  q must_pass e.
Proof.
intros ? ? ? ? Hbool Hmp.
dependent induction Hmp; eauto with mdb.
eapply m_step; eauto with mdb.
- destruct ex as [r trans]; inversion trans; subst.
  * inversion l; subst; eexists; constructor; eauto.
    rewrite Hbool in *; inversion H7.
  * eexists; eapply ParRight; eauto.
  * eexists; eapply ParSync; eauto.
    inversion l1; subst; eauto.
    rewrite Hbool in *; inversion H7.
- clear H1 com et H0.
  intros ? Hp.  
  eapply pt; eapply lts_ifZero; eauto.
- intros ? ? ? ? Hpi Hp He.
  eapply com; try eapply lts_ifZero; eauto.
Unshelve. apply (g 𝟘).
Qed. 
(*------------    composition    -------------------------*)
Proposition ctx_compose_iftrue: forall (p1 p2 q:proc) E,  
  p1 ⊑ p2 -> Eval_Eq E = Some true ->
  (If E Then p1 Else q) ⊑ (If E Then p2 Else q).
Proof.
repeat intro.
apply mp_iftrue; try apply H; auto.
eapply (mp_iftrue_rev _ _ _ _ H0 H1).
Qed.

Proposition ctx_compose_iffalse: forall (p q1 q2:proc) E,  
  q1 ⊑ q2 -> Eval_Eq E = Some false ->
  (If E Then p Else q1) ⊑ (If E Then p Else q2).
Proof.
repeat intro.
apply mp_iffalse; try apply H; auto.
eapply (mp_iffalse_rev _ _ _ _ H0 H1).
Qed.






















 
