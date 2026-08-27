


Require Import AltGenerality.



 
(*shift on trace*)
Fixpoint sh s := match s with
  | nil   => nil
  | mu::s' => (ash mu):: sh s'  
end.




(*==== a factoriser (existe aussi dans ctxchar) =======*)
Lemma dual_shift: forall mu1 mu2,
  dual mu1 mu2 ->
  dual (ash mu1) (ash mu2).
Proof. 
intros; cbv in H.
destruct mu1,mu2,a0; try (exfalso; apply H); subst; cbn; auto.
Qed.


Lemma dual_shift_inv: forall mu1 mu2, dual mu1 (ash mu2) ->
  exists mu0, mu1 = ash mu0 /\ dual mu0 mu2.
Proof.
intros ? ? Hdual.
destruct (inv_mu mu1) as [x [vx lem1]].
destruct (inv_mu mu2) as [y [vy lem2]].
destruct lem1,lem2; inversion H; inversion H0; subst;
cbn in *; try (exfalso; apply Hdual); subst.
- exists (Ainp y vy); split; cbn; try rewrite Hdual; auto.
- exists (Aout y vy); split; cbn; try rewrite Hdual; auto.
Qed.
(*=====================================================*)






(*-----------misc----------------------*)
Lemma inv_alpha: forall mu1 mu2,
  alpha (ash mu1) = alpha mu2 -> 
  exists mu0, mu2 = ash mu0 /\ alpha mu1 = alpha mu0 .
Proof.
intros ? ? Halph.
destruct (inv_mu mu1) as [x [vx lem1]].
destruct (inv_mu mu2) as [y [vy lem2]].
destruct lem1,lem2; inversion H; inversion H0; subst; 
cbn in *; inversion Halph; subst; eexists; erewrite delta_id; 
try (instantiate (1:= Ainp x vy); split; cbn; reflexivity); 
try (instantiate (1:= Aout x vy); split; cbn; reflexivity).
Qed.
 
Lemma nonref_nu: forall p mu, 
  ¬ (ν p) ↛[mu]  ->  ¬ p ↛[ash mu] .
Proof.
intros ? ? H. 
set (lem:= inv_nonmublock _ _ H).
destruct lem as [q [lem| lem]]; inversion lem; 
eauto using inv_nonmublock_rev.
Qed.

Lemma nonref_nu_rev: forall p mu, 
  ¬ p ↛[ash mu] -> ¬ (ν p) ↛[mu].
Proof.
intros ? ? H. 
set (lem:= inv_nonmublock _ _ H).
destruct lem as [q [lem| lem]]; 
apply lts_res_ext in lem;
eauto using inv_nonmublock_rev.
Qed.

Lemma blocking_shift: forall mu,
  blocking mu -> blocking (ash mu).
Proof.
intros ? Hblock. 
destruct (inv_mu mu) as [x [v lem]].
destruct lem; inversion H; subst; cbn in *; intro; 
inversion H0; inversion H1; subst.
assert (non_blocking_output (Aout x v)) by (cbv; eexists; auto); auto.
Qed.

Lemma blocking_shift_rev: forall mu,
  blocking (ash mu) -> blocking mu.
Proof.
intros ? Hblock. 
destruct (inv_mu mu) as [x [v lem]].
destruct lem; inversion H; subst; cbn in *; intro; 
inversion H0; inversion H1; subst.
assert (non_blocking_output (InputOutputActions.ActOut (VarC_add 1 x ⋉ v))). 
 by (cbv; eexists; auto). 
auto.
Qed.


(*----------------trace------------------------*)
Lemma shift_nil: forall s, nil=sh s -> s=nil.
Proof. 
intros ? H; destruct s; auto.
cbn in H; inversion H.
Qed.

Lemma shift_cons: forall mu s s', mu::s'=sh s -> 
  exists mu0 s0, s=mu0::s0 /\ 
  mu= ash mu0 /\ s'=sh s0.
Proof.
intros ? ? ? H; destruct s; cbn in *; 
inversion H; eauto.
Qed.
(*----------weak transitions ------------------*)

Lemma wt_unshift: forall p q s, wt p (sh s) q -> 
  wt (ν p) s (ν q).  
Proof.
intros ? ? ? Hwt.
dependent induction Hwt.
- apply shift_nil in x; subst; constructor.
- specialize (IHHwt s JMeq_refl);  
  eapply WeakTransitions.wt_tau;  
  try constructor; eauto. 
- apply shift_cons in x.
  destruct x as [mu0[s1[Heqs[Heqmu Heqs0]]]]; subst.
  specialize (IHHwt _ JMeq_refl).  
  eapply WeakTransitions.wt_act; 
  try constructor; eauto.
Qed.


Lemma wt_unshiftmu: forall p q mu, wt p [ash mu] q -> 
  wt (ν p) [mu] (ν q).  
Proof.
eauto using wt_unshift.
Qed.


Lemma wt_shift: forall p Q s, wt (ν p) s Q -> 
  exists p', wt p (sh s)  p' /\ Q=ν p'.
Proof.
intros ? ? ? Hwt.
dependent induction Hwt; eauto with mdb. 
- inversion l; subst. 
  specialize (IHHwt _ eq_refl). 
  destruct IHHwt as [p''[Hwtp' Heq]]. 
  eauto with mdb.
- inversion l; subst.
  specialize (IHHwt _ eq_refl).
  destruct IHHwt as [p''[Hwtp' Heq]]; subst. 
  exists p''; split; 
  try eapply WeakTransitions.wt_act; eauto.
Qed.

Lemma wt_shiftmu: forall p Q mu, wt (ν p) [mu] Q -> 
  exists p', wt p [ash mu]  p' /\ Q=ν p'.
Proof. 
intros ? ? ? H.
eauto using (wt_shift _ _ _ H).
Qed.
(*------------ convergence -----------------*)


Lemma term_nu: forall p, (ν p)⤓ -> p⤓.
Proof.
intros ? Hter; dependent induction Hter. 
constructor; intros p' Hp.
eapply H0; constructor; eauto.
Qed.

Lemma term_nu_rev: forall p, p⤓ -> (ν p)⤓.
Proof.
intros ? Hter; dependent induction Hter.
constructor; intros P Hnup; inversion Hnup.
eauto with mdb.
Qed.

Lemma cnv_nu: forall s p,
  (ν p)⇓s -> p⇓(sh s) .
Proof.
intros ? ?; generalize dependent p. 
induction s; intros ? Hcnv; 
inversion Hcnv; subst; cbn in *; 
try (constructor; auto using term_nu). 
intros p' Hwt; inversion Hwt; subst.
- eapply wt_unshiftmu in w.
  eapply IHs, H3, wt_unshiftmu; auto.
- apply lts_res_ext, mu_impl_wt in l.
  specialize (H3 _ l); specialize (IHs _ H3).
  eapply cnv_preserved_by_wt_nil; eauto.
Qed.

Lemma cnv_nu_rev: forall s p,
  p⇓(sh s) -> (ν p)⇓s.
Proof.
intros ? ? Hcnv.
dependent induction Hcnv.
- apply shift_nil in x; subst; constructor;
  auto using term_nu_rev.
- apply shift_cons in x; subst.
  destruct x as [mu0 [s1 [Heqs [Heqmu Heqs0]]]]; subst.
  constructor; auto using term_nu_rev.
  intros P Hwt; apply wt_shiftmu in Hwt.
  destruct Hwt as [p' [Hwt Heq]]; subst; eauto.
Qed.

(*-------------- composition --------------*)

Lemma lcnv_comp_nu: forall p q,
  p ≼₁ q ->  (ν p)  ≼₁ (ν q) . 
Proof.
unfold "≼₁"; intros ? ? Hplq ? Htaup.
eapply cnv_nu_rev, Hplq, cnv_nu; auto.
Qed.




Lemma lacc_comp_nu: forall p q,
  p ≼₂ q ->  (ν p)  ≼₂ (ν q) . 
Proof.
intros ? ? Hplq; unfold "≼₂"; intros ? Q Hcnv Hwt Href.
apply wt_shift in Hwt; apply cnv_nu in Hcnv.
unfold "≼₂" in Hplq; destruct Hwt as [q'[Hwt Heq]]; subst.
specialize (Hplq _ _ Hcnv Hwt); assert (q' ↛) by set_solver.
specialize (Hplq H); destruct Hplq as [p0 [Hwtp [Hrefp0 Hsubset]]]; subst.
exists (ν p0); repeat split; try (apply wt_unshift, Hwtp); try set_solver.
intros pmu Hpmu.
destruct Hpmu as [mu [Hcor Heq]].
destruct Hcor as [mu0 [Helt [Hdual Hblock]]].
assert ( (alpha (ash mu))∈ Alpha (Subset_Act.coR p0)).  
{ eexists; split; eauto.
  apply dual_shift in Hdual; apply blocking_shift in Hblock.
  exists (ash mu0); repeat split; 
  auto using nonref_nu.
} assert (alpha (ash mu) ∈ Alpha (Subset_Act.coR q')) by set_solver.
clear Hwtp Hrefp0 Hcnv Hwt Href H H0. 
destruct H1 as [mu1 [Hcor Halph]]; 
destruct Hcor as [mu2 [Helt2 [Hdual2 Hblock2]]].
apply inv_alpha in Halph; destruct Halph as [mu3 [Heq2 Halph]]; subst.
apply dual_shift_inv in Hdual2; 
destruct Hdual2 as [mu4 [Heq Hdual2]]; subst.
eexists; split; eauto.  
eexists; repeat split; eauto using nonref_nu_rev. 
apply blocking_shift_rev; auto.
Qed.

 
Proposition alt_comp_nu: forall p q, 
  p ≼ₐₛ q -> ν p ≼ₐₛ ν q.
Proof.
unfold "≼ₐₛ"; intros.
split; try apply lcnv_comp_nu; 
try apply lacc_comp_nu; apply H.
Qed.
