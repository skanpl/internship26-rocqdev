
Require Import CtxGenerality.



Notation ash mu :=  (VarC_action_add 1 mu).



(*==== a factoriser (existe aussi dans altchar) =======*)
Lemma inv_mu: forall mu:InputOutputActions.ExtAct TypeOfActions,
  exists x v, ( ActExt mu = Linp x v) \/  
              (ActExt mu = Lout x v)   .
Proof.
intros; destruct mu,a; eauto.
Qed.

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
- exists ( InputOutputActions.ActIn (y ⋉ vy)); 
  split; cbn; try rewrite Hdual; auto.
- exists ( InputOutputActions.ActOut (y ⋉ vy)); 
  split; cbn; try rewrite Hdual; auto.
Qed.
(*============== admitted properties ================*)

Fixpoint shift (p:proc) : proc. Admitted.


Lemma lts_shift_mu: forall (p q:proc) mu,
  lts p (ActExt mu) q -> lts (shift p) (ActExt ( ash mu)) (shift q).
Proof.  Admitted.

Lemma lts_shift_tau: forall (p q:proc),
  lts p τ q -> lts (shift p) τ (shift q).
Proof. Admitted.

Lemma lts_shift_inv_tau: forall (p q:proc), lts (shift p) τ q -> 
  exists p', lts p τ p' /\ q = shift p'.
Proof. Admitted.

 
Lemma lts_shift_inv_mu: forall (p q:proc) mu, 
  lts (shift p) (ActExt mu) q -> 
  exists p' mu0, lts p (ActExt mu0) p' /\ q = shift p' /\ mu= ash mu0.
Proof. Admitted.

Lemma good_shift: forall (e:proc), 
  good_VACCS e <-> good_VACCS (shift e).
Proof. 
(*NB to prove this you need to generalize from shift to an 
  arbitrary substitution sigma because of lifting.
*) 
Admitted.

(*=========== new compose tentatives   ====================*)
 


Lemma ash_inj: forall mu1 mu2,  (* maybe useless lemma *)
  ash mu1 = ash mu2 -> mu1=mu2.
Proof.
intros; unfold ash in H.
destruct mu1,mu2,a,a0; inversion H; subst.
cbv in H1; destruct c,c0; inversion H ; auto.
unfold VarC_add in H1; destruct c,c0; inversion H; auto.
Qed.



Lemma mp_tonu: forall (p e: proc),
  p must_pass shift e -> ν p must_pass e.
Proof.
intros.
dependent induction H; eauto with mdb.
- eapply m_now; destruct (good_shift e); firstorder.
- eapply m_step.
  * destruct (good_shift e); clear pt H et H0 com H1 ex; firstorder.
  * destruct ex as [r trans]; inversion trans; subst.
    + eexists; do 2 constructor; eauto.
    + set (lem:= lts_shift_inv_tau _ _ l); destruct lem as [e0 [G1 G2]]; 
      eexists; eapply ParRight; eauto.
    + set (leme:= lts_shift_inv_mu _ _ _ l2).
      destruct leme as [e' [mu0 [He [b2eq mu2eq]]]]; subst.
      set (lem:= dual_shift_inv _ _ eq).
      destruct lem as [mu1 [mu1eq Hpi12]]; subst.
      eexists; eapply ParSync; eauto.
      constructor; eauto.
  * intros P Hnup.    
    inversion Hnup; subst; eauto.
  * intros e' He.
    eapply H0; try eapply lts_shift_tau; eauto.
  * intros P e' ? ? Hpi Hnup He.
    set (lem:= dual_shift _ _ Hpi). 
    inversion Hnup; subst.
    eapply H1; try apply lem; try eapply lts_shift_mu ; eauto.
Qed.




Lemma mp_fromnu: forall (p e: proc),
  ν p must_pass e -> p must_pass shift e.
Proof.
intros.
dependent induction H; eauto with mdb.
- eapply m_now; destruct (good_shift t); firstorder.
- eapply m_step.
  * destruct (good_shift t); clear pt H et H0 com H1 ex; firstorder.
  * destruct ex as [r trans]; inversion trans; subst.
    + inversion l; subst; eexists; constructor; eauto.
    + eexists; eapply ParRight; set (lem:= lts_shift_tau _ _ l); eauto.
    + inversion l1; subst. set (lem:= lts_shift_mu _ _ _ l2);
      eexists; eapply ParSync; try eapply dual_shift; eauto.
  * intros p' Hp.
    eapply H; try constructor; eauto.
  * intros e' Hse.
    set (lem:= lts_shift_inv_tau _ _ Hse).
    destruct lem as [e1 [He Heeq]]; subst; eauto.
  * intros p' E ? ? Hpi Hp Hse.  
    set (lem:= lts_shift_inv_mu _ _ _ Hse).
    destruct lem as [e' [mue [He [Hsh Hash]] ]]; subst.
    set (lem:= dual_shift_inv _ _ Hpi). 
    destruct lem as [mup [Hash Hpipe]]; subst.
    eapply H1; try apply Hpipe; try constructor; eauto.
Qed.       





Proposition  ctx_compose_nu: forall (p q: proc),
  p ⊑ q -> (ν p) ⊑ (ν q). 
Proof.
unfold "⊑"; intros; 
apply (mp_tonu _ _ (H _ (mp_fromnu _ _ H0))).
Qed.





