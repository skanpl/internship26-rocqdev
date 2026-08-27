

Require Import AltGenerality.







(*====================   tau   ==============================*)

(*-------------- convergence lemmas ---------------*)

Lemma term_tau: forall p:proc, (tau p) ⤓ -> p⤓.
Proof.
intros ? H; inversion H.
eapply H0; constructor.
Qed.

Lemma term_tau_rev: forall p:proc, p⤓ -> (tau p)⤓.
Proof.
intros; constructor; intros ? Htau. 
inversion Htau; subst; auto.
Qed.

Lemma cnv_tau: forall p s,
  (tau p)⇓s -> p⇓s.
Proof.
intros.
set (lem:= cnv_preserved_by_lts_tau _ _ H p).
eapply lem; constructor. 
Qed.

Lemma cnv_tau_rev: forall p s,
  p⇓s -> (tau p)⇓s.
Proof.
intros ? ? Hp.
dependent induction Hp; constructor; 
eauto using term_tau_rev.
intros ? Hwt.
inversion Hwt; inversion l; subst.
eapply H0; auto.
Qed.
(*-----------------------------------------*)
 

Lemma lcnv_comp_tau: forall p q,
  p ≼₁ q ->  (tau p)  ≼₁ (tau q) . 
Proof.
unfold "≼₁"; intros ? ? Hplq ? Htaup.
eapply cnv_tau_rev, Hplq, cnv_tau; auto.
Qed.

Lemma lacc_comp_tau: forall p q,
  p ≼₂ q ->  (tau p)  ≼₂ (tau q) . 
Proof.
intros ? ? Hplq. 
unfold "≼₂".
intros s ? Hcnv Hwt Href.
inversion Hwt; try inversion l; subst.
- inversion Href.
- unfold "≼₂" in Hplq.
  eapply cnv_tau in Hcnv.
  specialize (Hplq _ _ Hcnv w Href).
  destruct Hplq as [P [Hwtp [HPref Hsubset]]].
  exists P; repeat split; eauto.
  eapply WeakTransitions.wt_tau; eauto; constructor.
Qed.
  
Proposition alt_comp_tau: forall p q, 
  p ≼ₐₛ q -> tau p ≼ₐₛ tau q.
Proof.
unfold "≼ₐₛ"; intros.
split; try apply lcnv_comp_tau; 
try apply lacc_comp_tau; apply H.
Qed.



(*====================   input   ==============================*)


Lemma wt_inp: forall x q Q mu s,  wt (inp x q) (mu::s) Q -> 
  exists v:Data, ActExt mu = Linp x v /\ wt (sub q v) s Q.
Proof.
intros ? ? ? ? ? Hwt.
inversion Hwt; inversion l; subst.
eexists; split; eauto.
Qed.



Lemma lcnv_comp_inp: forall x p q,
 (forall v, sub p v ≼₁ sub q v) ->  inp x p  ≼₁ inp x q. 
Proof.
unfold "≼₁"; intros ? ? ? Hplq ? Hinp.
destruct s; constructor. 
- constructor; intros ? Hexfal; inversion Hexfal.
- constructor; intros ? Hexfal; inversion Hexfal.
- intros Q Hwt; set (lem:= wt_inp _ _ _ _ _ Hwt).
  destruct lem as [v [Heq Hwtnil]].
  inversion Hinp; inversion Heq; subst.
  specialize (H3 (sub p v)).
  assert (wt (inp x p) [Ainp x v] (sub p v)).
  eapply mu_impl_wt; constructor.
  specialize (Hplq _ _ (H3 H)).
  eapply cnv_preserved_by_wt_nil; eauto.
Qed.





Lemma lacc_comp_inp: forall x p q,
 (forall v, sub p v ≼₂ sub q v) ->  inp x p  ≼₂ inp x q. 
Proof.
intros ? ? ? Hplq.
unfold "≼₂"; intros ? Q Hcnv Hwt Href. 
destruct s. 
- exists (inp x p); repeat split; eauto; try constructor.
  inversion Hwt; try inversion l; subst. 
  clear Hwt Href Hcnv Hplq; repeat intro. 
  destruct H as [mu [Hcor Heq]]; subst. 
  exists mu; split. 
  + destruct Hcor as [mu0 [G1 [G2 G3]]].
    unfold "blocking", non_blocking, non_blocking_output, 
    InputOutputActions.is_output in *.
    destruct (inv_mu mu) as  [c [v inv_mu]].
    destruct inv_mu as [inv_mu|inv_mu].
    * inversion inv_mu; subst; clear inv_mu.
      destruct (inv_mu mu0) as  [c0 [v0 inv_mu0]].
      destruct inv_mu0 as [inv_mu0|inv_mu0]; subst;
      inversion inv_mu0; subst; cbv in G2; 
      try (exfalso; auto); set_solver.
    * exfalso; apply G3; exists (act c v); 
      inversion inv_mu; auto.
  + unfold 𝝳ᴠᴀᴄᴄꜱ, "∘", Φᴠᴀᴄᴄꜱ; destruct mu,a; auto.      
- set (lem:= wt_inp _ _ _ _ _ Hwt).
  destruct lem as [v [Heq Hwtsub]].
  inversion Heq; subst.
  inversion Hcnv; subst.
  specialize (H3 (sub p v)).
  assert (wt (inp x p) [Ainp x v] (sub p v)).
  eapply mu_impl_wt; constructor.
  specialize (H3 H).
  unfold "≼₂" in Hplq.
  specialize (Hplq _ _ _ H3 Hwtsub Href).
  destruct Hplq as[P[Hwtp [HPref Hsubset]]].
  exists P; repeat split; eauto.
  eapply WeakTransitions.wt_act; try constructor; eauto.
Qed.


Proposition alt_comp_inp: forall x p q,
  (forall v, sub p v ≼ₐₛ sub q v) -> inp x p ≼ₐₛ inp x q. 
Proof.
unfold "≼ₐₛ"; intros ? ? ? Hplq; split;
try eapply lcnv_comp_inp; try eapply lacc_comp_inp; apply Hplq.
Qed.


(*=================   sum   ======================*)


(* ----  weak transitions ----------*)
Lemma wt_sum: forall p q r mu s, 
  wt (sum p q) (mu::s) r -> 
  wt (g p) (mu::s) r \/ wt (g q) (mu::s) r.
Proof.
intros ? ? ? ? ? Hwt. 
inversion Hwt; inversion l; eauto with mdb.
Qed.

Lemma wt_sumL_rev: forall p q r mu s,
  wt (g p) (mu::s) r -> wt (sum p q) (mu::s) r.
Proof.
intros ? ? ? ? ? Hwt; inversion Hwt; subst.
- econstructor. econstructor. apply l. apply w.
- eapply WeakTransitions.wt_act; eauto.
  constructor; auto.
Qed.


Lemma wt_sumR_rev: forall p q r mu s,
  wt (g q) (mu::s) r -> wt (sum p q) (mu::s) r.
Proof.
intros ? ? ? ? ? Hwt; inversion Hwt; subst.
- econstructor. apply lts_choiceR. apply l. apply w.
- eapply WeakTransitions.wt_act; eauto.
  apply lts_choiceR; auto.
Qed.


Lemma wt_summu: forall p q r mu, 
  wt (sum p q) [mu] r -> 
  wt (g p) [mu] r \/ wt (g q) [mu] r.
Proof.
auto using wt_sum.
Qed.

Lemma wt_summuL_rev: forall p q r mu,
  wt (g p) [mu] r -> wt (sum p q) [mu] r.
Proof.
auto using wt_sumL_rev.
Qed.


Lemma wt_summuR_rev: forall p q r mu,
  wt (g q) [mu] r -> wt (sum p q) [mu] r.
Proof.
auto using wt_sumR_rev.
Qed.



Lemma wt_sumnil: forall p q r, 
  wt (sum p q) nil r -> 
  r = sum p q  \/  wt (g p) nil r \/ wt (g q) nil r.
Proof.
intros ? ? ? Hwt.
inversion Hwt; try inversion l; eauto with mdb.
Qed.

(*------ convergence ----------*)

Lemma term_sum: forall p q,
  (sum p q) ⤓ ->  (g p)⤓ /\ (g q)⤓. 
Proof.
intros ? ? Hsum; inversion Hsum.
 split; constructor; intros ? Hlt; apply H. 
- apply lts_choiceL; auto. 
- apply lts_choiceR; auto. 
Qed.

Lemma term_sum_rev: forall p q,
  (g p)⤓ -> (g q)⤓ -> (sum p q) ⤓ . 
Proof.
intros ? ? Hp Hq.
constructor; intros ? Hsum; inversion Hsum; 
try inversion l; auto.
- apply Hp; auto.
- apply Hq; auto.
Qed.

Lemma cnv_sum: forall p q s,
  (sum p q)⇓s ->  (g p)⇓s /\ (g q)⇓s .
Proof.
intros ? ? ? Hcnv.
destruct s; inversion Hcnv; split; constructor; subst;  
try ( first 
  [set (lem:= term_sum p q H)| 
   set (lem:= term_sum p q H2)]; 
destruct lem); auto; intros ? Hwt; inversion Hcnv; apply H7. 
- apply wt_summuL_rev; auto.
- apply wt_summuR_rev; auto.
Qed.

Lemma cnv_sum_rev: forall p q s,
  (g p)⇓s -> (g q)⇓s -> (sum p q)⇓s.
Proof.
intros ? ? ? Hpcnv Hcnvq; destruct s; constructor; 
inversion Hpcnv; inversion Hcnvq; auto using term_sum_rev.
intros ? Hwt; apply wt_summu in Hwt; destruct Hwt; auto.
Qed.

Lemma lcnv_comp_sum: forall p1 p2 q,
  g p1 ≼₁ g p2 ->  (sum p1 q)  ≼₁ (sum p2 q) . 
Proof.
unfold "≼₁"; intros ? ? ? Hplq ? Hsum.
apply cnv_sum in Hsum; destruct Hsum; 
apply cnv_sum_rev; auto.
Qed.

Definition isum (p q: proc) := sum (gtau p) (gtau q).
(*============== a factoriser================*)
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

Lemma ref_exf: forall p p', 
  p ↛ -> lts p Ltau p' -> False.
Proof.
intros; inversion H.
eapply lts_set_tau_spec1 in H0; set_solver.
Qed.


Lemma isum_invert: forall (p q r: proc), (isum p q)  ⟶  r -> 
  r= p \/ r=q.
Proof.
intros ? ? ? Hisum.
inversion Hisum; subst; inversion H3; subst.
- left; auto.
- right; auto.
Qed.
(*=================================================*)

 

Lemma wt_isumL: forall p p' q s,
  wt p s p' -> wt (isum p q) s p'. 
Proof.
intros ? ? ? ? Hwt.
eapply WeakTransitions.wt_tau; 
eauto using isuml.
Qed.


Lemma wt_isumR: forall p q q' s,
  wt q s q' -> wt (isum p q) s q'. 
Proof.
intros ? ? ? ? Hwt.
eapply WeakTransitions.wt_tau; 
eauto using isumr.
Qed.

Lemma lacc_comp_isum: forall p1 p2 q,
  p1 ≼₂ p2 ->  (isum p1 q)  ≼₂ (isum p2 q) . 
Proof.
intros ? ? ? Hlac; unfold "≼₂".
intros ? Q Hcnv Hwt Href.
inversion Hwt; subst; eauto with mdb.
- eapply ref_exf in Href; try eapply isuml; 
  exfalso; auto.
- set (lem:= isum_invert _ _ _ l).
  destruct lem as [lem|lem]; subst.
  + apply cnv_sum in Hcnv; destruct Hcnv as [Hcnv _].
    apply cnv_tau in Hcnv; unfold "≼₂" in Hlac. 
    specialize (Hlac _ _ Hcnv w Href).
    destruct Hlac as [P [Hp1 [HPref Halsub]]].
    exists P; auto using wt_isumL.
  + exists Q; auto using wt_isumR.
- inversion l; inversion H3. 
Qed.


Lemma lcnv_comp_isum: forall p1 p2 q,
  p1 ≼₁ p2 ->  (isum p1 q)  ≼₁ (isum p2 q) . 
Proof.
intros.
eapply lcnv_comp_sum, lcnv_comp_tau; auto.
Qed.

Proposition alt_comp_isum: forall p1 p2 q, 
  p1 ≼ₐₛ p2 -> (isum p1 q) ≼ₐₛ (isum p2 q).
Proof.
unfold "≼ₐₛ"; intros.
split; try apply lcnv_comp_isum; 
try apply lacc_comp_isum; apply H.
Qed.
