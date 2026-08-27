


Require Import CtxGenerality.



Lemma inp_nil: forall c v, lts (inp c 𝟘) (Linp c v) (sub  (g 𝟘) v) .
Proof.
intros; cbv; eauto with mdb.
Qed.  




(*============== ~(0 ⊑c!v) =============*)
Lemma cep1: forall (c : ChannelData),
  (g 𝟘) must_pass   sum (gtau ①) (ginp c 𝟘). 
Proof.
intro.
eapply m_step.
intro.
inversion H; subst.
- destruct H1; inversion H0.
- eexists; eapply ParRight;  eapply lts_choiceL; eauto with mdb.
- intros; inversion H.
- intros; inversion H; subst; inversion H4; subst; 
  apply m_now; eauto with ccs.
- intros; inversion H0.
Qed.



Lemma cep2: forall (c : ChannelData) (v:Data),
  ~ (out c v) must_pass   sum (gtau ①) (ginp c 𝟘). 
Proof.
intros. intro.
inversion H.
- inversion H0; subst; inversion H2; inversion H1.
- specialize (com 𝟘 𝟘). 
  assert (g 𝟘 must_pass g 𝟘).
  eapply com. 
  Focus 2. 
  eapply lts_output.
  Focus 2. 
  eapply lts_choiceR.         
  eapply inp_nil.
  unfold  dual; simpl; eauto.
  inversion H0; try inversion H1.
  destruct ex0 as [r trans]; inversion trans; subst; 
  try inversion l; try inversion l1.
Qed.


Proposition ce: forall (c : ChannelData) (v:Data),
  ~ (g 𝟘) ⊑ out c v.
Proof.
intros. intro.
unfold "⊑" in H.
specialize (H _ (cep1 c)).
eapply cep2; eauto.
Qed.

(*=================  ~(0 ⊑ c?(x).𝟘)  =================================*)  
Lemma ce2p1: forall (c : ChannelData) v,
  (g 𝟘) must_pass (out c v)‖ (inp c ①). 
Proof.
intros.
eapply m_step.
- intro; inversion H; subst; destruct H1; inversion H0.
- eexists; eapply ParRight; econstructor; eauto with mdb.
- intros; inversion H.
- intros; inversion H; subst; try inversion H2; try inversion H3; 
  subst; try inversion H4.
  simpl; eapply m_now; constructor; right; constructor.
- intros; inversion H0.
Qed.
    

Lemma ce2p2: forall (c : ChannelData) v,
 ~ inp c 𝟘 must_pass  (out c v)‖ (inp c ①). 
Proof.
intros. intro.
inversion H.
- inversion H0; subst; destruct H2; inversion H1.
- assert ((g 𝟘) must_pass  (g 𝟘)‖ g (gpr_input c ①)). 
  eapply com; try eapply inp_nil; try econstructor; eauto with mdb; cbv; eauto.
  inversion H0.  
  * inversion H1; subst; destruct H3; inversion H2. 
  * destruct ex0 as [r trans]; inversion trans; subst.
    + inversion l.
    + inversion l; subst; try inversion H5. 
      inversion H3. inversion H4. 
    + inversion l1.
Qed.
    
Proposition ce2: forall (c : ChannelData) (v:Data),
  ~  (g 𝟘) ⊑ inp c 𝟘 .
Proof.
intros. intro.
unfold "⊑" in H.
specialize (H _ (ce2p1 c v)).
eapply ce2p2; eauto.
Qed.

(*===============   p+q ⊑ p not true in general   ==========================*)


Lemma ce3p1: forall (c : ChannelData) v,
  sum 𝟘 (gtau (out c v))  must_pass inp c ①. 
Proof.
intros.
apply m_step.
- intro; inversion H.
- eexists; constructor. 
  eapply lts_choiceR; eauto with mdb.
- intros; inversion H; inversion H4; subst; eapply m_step.
  * intro; inversion H0.
  * eexists; eapply ParSync; try econstructor; cbv; eauto.
  * intros; inversion H0.
  * intros; inversion H0.
  * intros. inversion H2; subst; cbn; eapply m_now; constructor. 
- intros; inversion H.
- intros ? ? ? ? Hpi Hsum Hinp. 
  inversion Hsum; subst; inversion H3.
Qed.

Lemma ce3p2: forall (c : ChannelData),
  ~ (g 𝟘) must_pass   inp c ①. 
Proof.
repeat intro. 
inversion H.
- inversion H0.
- destruct ex as [r trans]; inversion trans; subst; 
  try inversion l; try inversion l1.
Qed.

Lemma ce3: forall c v, 
  ~ sum 𝟘 (gtau (out c v))  ⊑ g 𝟘 .
Proof.
unfold "⊑"; repeat intro.
specialize (H _ (ce3p1 c v)).
eapply ce3p2; eauto.
Qed.

(*===================== + does not compose ================================*)



Lemma part1: forall x v, 
  sum 𝟘 (gtau (out x v))  must_pass   inp x ①.  
Proof.
intros; apply m_step.
- intro; inversion H.
- eexists; constructor; apply lts_choiceR; constructor.
- intros; inversion H; inversion H4; subst; apply m_step.
  * intro Hg; inversion Hg.
  * eexists; eapply ParSync; try constructor; cbv; auto.
  * intros ? Hout; inversion Hout.
  * intros ? Hinp; inversion Hinp.
  * intros ? ? ? ? ? ? Hinp; inversion Hinp; 
    cbn; do 2 constructor.
- intros ? Hinp; inversion Hinp.
- intros ? ? ? ? ? ? Hinp; inversion Hinp; 
  cbn; do 2 constructor.
Qed.


Lemma part2: forall x v, 
  ~  sum (gtau (g 𝟘)) (gtau (out x v))  must_pass   inp x ①.  
Proof.
intros ? ? Hmp; inversion Hmp; try inversion H.
assert (sum (gtau 𝟘) (gtau (out x v)) ⟶ 𝟘); try do 2 constructor.
specialize (pt _ H); inversion pt; try inversion H0.
destruct ex0 as [t Htrans]; inversion Htrans; try inversion l.
inversion l1.
Qed.



Require Import CtxCompose.
Lemma nil_less_taunil: (g 𝟘) ⊑ tau (g 𝟘).
Proof.
intro; auto using mp_tau.
Qed.  

Lemma compose_fail: forall x v,
  ~ sum 𝟘 (gtau (out x v)) ⊑ sum (gtau (g 𝟘)) (gtau (out x v)).
Proof.
intros ? ? Hmust.
unfold "⊑" in Hmust.
specialize (Hmust _ (part1 x v)).
eapply part2, Hmust.
Qed.
