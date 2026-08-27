

Require Import AltGenerality.
 






(*============ weak transitions ==============*)

Lemma lts_com: forall p p' q q' mup muq, 
  lts p (ActExt mup) p' -> lts q (ActExt muq) q' -> 
  dual mup muq ->
  lts (p‖q) Ltau (p'‖q').
Proof.
intros ? ? ? ? ? ? Hp Hq Hdual.
set (lemp:= inv_mu mup); set (lemq:= inv_mu muq).
destruct lemp as [x [vx lemp]]. 
destruct lemq as [y [vy lemq]].
destruct lemp,lemq; inversion H0; inversion H; subst; 
cbn in *; try (exfalso; apply Hdual); 
inversion Hdual; subst; eauto with mdb.
Qed.

Lemma wt_parL: forall p p' q s, 
  wt p s p' -> wt (p ‖ q) s (p' ‖ q).
Proof.
intros ? ? ? ? Hwt.
dependent induction Hwt; eauto with mdb.
- eapply WeakTransitions.wt_tau; try eapply lts_parL; eauto.
- eapply WeakTransitions.wt_act; try eapply lts_parL; eauto.
Qed.

Lemma wt_parR: forall p q q' s, 
  wt q s q' -> wt (p ‖ q) s (p ‖ q').
Proof.
intros ? ? ? ? Hwt.
dependent induction Hwt; eauto with mdb.
- eapply WeakTransitions.wt_tau; try eapply lts_parR; eauto.
- eapply WeakTransitions.wt_act; try eapply lts_parR; eauto.
Qed.

Lemma wt_invpar: forall p q s Q, 
  wt (p‖q) s Q -> exists p' q', Q=p'‖q'.
Proof. 
intros ? ? ? ? Hwt; dependent induction Hwt; eauto;
inversion l; subst; eapply IHHwt; eauto.
Qed.

Lemma wt_parmerge: forall p q p' q' sp sq,
  wt p sp p' -> wt q sq q' -> 
  wt (p‖q) (sp++sq) (p'‖q').
Proof.
intros ? ? ? ? ? ? Hp.
dependent induction Hp; intros Hq; 
cbn in *; try specialize (IHHp Hq). 
- eauto using wt_parR.
- eapply WeakTransitions.wt_tau; 
  try eapply lts_parL; eauto.
- eapply WeakTransitions.wt_act; 
  try eapply lts_parL; eauto.
Qed.
 
Lemma wt_eventually: forall p p' mu,
 wt p [mu] p' ->  exists p1 p2,
 wt p [] p1  /\ lts p1 (ActExt mu) p2 /\ wt p2 [] p'.
Proof.
intros.
dependent induction H.
- specialize (IHwt _ JMeq_refl).
  destruct IHwt as [p1 [p2 [Hq [Hlt Hp2]]]].
  exists p1,p2; repeat split; auto.
  eapply WeakTransitions.wt_tau; eauto.
- exists p,q; eauto with mdb.
Qed.




Lemma wt_cancel: forall p q p' q' mup muq sp sq,
  wt p (mup::sp) p' -> wt q (muq::sq) q' -> 
  dual mup muq -> 
  wt (p‖q) (sp++sq) (p'‖q').
Proof. 
intros ? ? ? ? ? ? ? ? Hwtp Hwtq Hdual.
replace (mup::sp) with ([mup]++sp) in Hwtp; auto.
replace (muq::sq) with ([muq]++sq) in Hwtq; auto.
apply WeakTransitions.wt_split in Hwtp, Hwtq.
destruct Hwtp as [p0 [Hwtp Hwtp0]].
destruct Hwtq as [q0 [Hwtq Hwtq0]].
apply wt_eventually in Hwtp, Hwtq.
destruct Hwtp as [a [b [Hwtp [Hltp Hwtp2]]]].
destruct Hwtq as [c [d [Hwtq [Hltq Hwtq2]]]].
assert (lts (a‖c) Ltau (b‖d)) by (eapply lts_com; eauto).
assert (wt (a‖c) [] (b‖d)) by eauto with mdb.
assert (wt (p‖q) [] (a‖c)) by 
  (apply (wt_parmerge _ _ _ _ [] []); eauto). 
set (lem:=  WeakTransitions.wt_concat _ _ _ _ _ H1 H0); cbn in lem.
assert (wt (b‖d) [] (p0‖q0)) by 
  (apply (wt_parmerge _ _ _ _ [] []); eauto).
set (lem2:=  WeakTransitions.wt_concat _ _ _ _ _ lem H2); cbn in lem2.
set (finmerge:= wt_parmerge _ _ _ _ _ _ Hwtp0 Hwtq0).
apply (WeakTransitions.wt_concat _ _ _ _ _ lem2 finmerge).
Qed.
(*============== convergence ===================*)
Lemma term_parL: forall p q,  (p‖q)⤓ -> p⤓ .
Proof.
intros ? ? H.
dependent induction H; constructor.
intros p' Hp.
eapply H0; constructor; auto.
Qed.

Lemma term_parR: forall p q,  (p‖q)⤓ -> q⤓ .
Proof.
intros ? ? H.
dependent induction H; constructor.
intros p' Hp.
eapply H0; constructor; auto.
Qed.

Lemma cnv_parL: forall p q s, (p‖q)⇓s ->  p⇓s.
Proof.
intros ? ? ? Hcnv.
dependent induction Hcnv; constructor; eauto using term_parL.
intros p' Hwt.
eapply H1; eauto with mdb.
eauto using wt_parL.
Qed.

Lemma cnv_parR: forall p q s, (p‖q)⇓s ->  q⇓s.
Proof.
intros ? ? ? Hcnv.
dependent induction Hcnv; constructor; eauto using term_parR.
intros q' Hwt.
eapply H1; eauto with mdb.
eauto using wt_parR.
Qed.
(*=================  zipping ===================*)

 
Inductive zip: trace vact -> trace vact -> trace vact -> Prop :=
| zip_nil: zip [] [] []
| zip_consL: forall s s1 s2 mu,
    zip s s1 s2 -> zip (mu::s) (mu::s1) s2 
| zip_consR: forall s s1 s2 mu,
    zip s s1 s2 -> zip (mu::s) s1 (mu::s2) 
| zip_consLR: forall s s1 s2 mu1 mu2,
    zip s s1 s2 -> dual mu1 mu2 -> 
    zip s (mu1::s1) (mu2::s2) 
.

Hint Constructors zip:mdb.


(*----- basic zipping properties ------*)
Lemma zip_idL: forall s, zip s s [].
Proof. 
induction s; eauto with mdb.
Qed.

Lemma zip_idR: forall s, zip s [] s.
Proof. 
induction s; eauto with mdb.
Qed.

Lemma dual_commut: forall mu1 mu2, 
  dual mu1 mu2 -> dual mu2 mu1.
intros.
destruct mu1,mu2,a,a0; cbn; eauto with mdb.
Qed.

Lemma zip_commut: forall s s1 s2, 
  zip s s1 s2 -> zip s s2 s1.
Proof.
intros ? ? ? Hzip; induction Hzip; eauto with mdb.
apply zip_consLR; eauto using dual_commut.
Qed.
(*----- lemmes fondamentaux du zipping  -----*)

Lemma unzip_wt: forall (p q p' q':proc) s,
  wt (p‖q) s (p'‖q')  -> 
  exists s1 s2, 
  zip s s1 s2 /\ wt p s1 p' /\  wt q s2 q'. 
Proof.
intros ? ? ? ? ? Hwt. 
dependent induction Hwt.
- exists [],[]; eauto with mdb.
- inversion l; subst; 
  specialize (IHHwt _ _ _ _ eq_refl eq_refl);
  destruct IHHwt as [s1 [s2 [Hzip [Hw1 Hw2]]]].
  + exists ((Aout c v)::s1),
           ((Ainp c v)::s2).
    repeat split; inversion Hwt; subst; try eapply zip_consLR; 
    try apply zip_nil; cbn; eauto with mdb.
  + exists ((Ainp c v)::s1),
           ((Aout c v)::s2).
    repeat split; inversion Hwt; subst; try eapply zip_consLR; 
    try apply zip_nil; cbn; eauto with mdb.
  + eexists; eauto with mdb.
  + eexists; eauto with mdb.
- inversion l; subst; 
  specialize (IHHwt _ _ _ _ eq_refl eq_refl);
  destruct IHHwt as [s1 [s2 [Hzip [Hw1 Hw2]]]].
  + exists (μ::s1),s2; eauto with mdb.
  + exists s1,(μ::s2); eauto with mdb.
Qed.

 
Lemma zip_wt: forall (p q p' q':proc) s s1 s2,
  zip s s1 s2 -> wt p s1 p' ->  wt q s2 q' ->
  wt (p‖q) s (p'‖q'). 
Proof.
intros ? ? ? ? ? ? ? Hzip. 
revert p q p' q'.
dependent induction Hzip; intros ? ? ? ?  Hp Hq.
- eapply (wt_parmerge _ _ _ _ _ _ Hp Hq).
- replace (mu::s1) with ([mu]++s1) in Hp; auto.
  apply WeakTransitions.wt_split in Hp.
  destruct Hp as [a [Hp Ha]].
  specialize (IHHzip _ _ _ _ Ha Hq).
  assert (wt q [] q) by eauto with mdb.
  set (lem:= wt_parmerge _ _ _ _ _ _ Hp H); cbn in lem.
  apply (WeakTransitions.wt_concat _ _ _ _ _ lem IHHzip).
- replace (mu::s2) with ([mu]++s2) in Hq; auto.
  apply WeakTransitions.wt_split in Hq.
  destruct Hq as [a [Hq Ha]].
  specialize (IHHzip _ _ _ _ Hp Ha).
  assert (wt p [] p) by eauto with mdb.
  set (lem:= wt_parmerge _ _ _ _ _ _ H Hq); cbn in lem.
  apply (WeakTransitions.wt_concat _ _ _ _ _ lem IHHzip). 
- replace (mu1::s1) with ([mu1]++s1) in Hp; auto.
  replace (mu2::s2) with ([mu2]++s2) in Hq; auto.
  apply WeakTransitions.wt_split in Hp, Hq.
  destruct Hp as [p0 [Hp Hp0]].
  destruct Hq as [q0 [Hq Hq0]].
  specialize (IHHzip _ _ _ _ Hp0 Hq0).
  set (lem:= wt_cancel _ _ _ _ _ _ _ _ Hp Hq H); cbn in lem. 
  apply (WeakTransitions.wt_concat _ _ _ _ _ lem IHHzip).
Qed.
(*============= tentative avec nocom ========================*)

(*----------- ewt -----------------------*)
Definition ewt p s := exists q, wt p s q.

Lemma exitst_wt: forall p p' mu,
  lts p (ActExt mu) p' -> ewt p [mu] .
Proof.
unfold ewt; eauto with mdb.
Qed.

Lemma ewt_later: forall p p' s,
  lts p Ltau p' -> ewt p' s -> ewt p s.
unfold ewt; intros ? ? ? ? Hew.
destruct Hew; eauto with mdb.
Qed.
(*--------- nocom  ------------------------*)

Definition nocom p q := forall s1 s2 s1' s2' mup muq,
  ewt p (s1++[mup]++s2) -> ewt q (s1'++[muq]++s2') ->
   ~ dual mup muq . 



Lemma nocom_ltL: forall p p' q, nocom p q -> 
  lts p Ltau p'  -> nocom p' q.
Proof.
unfold nocom; intros ? ? ? Hnc Hlt.
intros ? ? ? ? ? ? Hewp Hewq.
set (lem:= ewt_later _ _ _ Hlt Hewp); eauto.
Qed.

Lemma nocom_ltR: forall p q q', nocom p q -> 
  lts q Ltau q'  -> nocom p q'.
Proof.
unfold nocom; intros ? ? ? Hnc Hlt.
intros ? ? ? ? ? ? Hewp Hewq.
set (lem:= ewt_later _ _ _ Hlt Hewq); eauto.
Qed.

Lemma nocom_wtL: forall p p' q s, nocom p q ->
  wt p s p' -> nocom p' q.
Proof.
unfold nocom; intros ? ? ? ? Hnc Hwt.
intros ? ? ? ? ? ? Hewp Hewq.
unfold ewt in Hewp.
destruct Hewp as [p'' Hp'].
set (lem:= WeakTransitions.wt_concat _ _ _ _ _ Hwt Hp'). 
replace (s ++ s1 ++ [mup] ++ s2) with 
  ((s ++ s1) ++ [mup] ++ s2) in lem by 
  (cbn; rewrite app_assoc; auto).
assert (ewt p ((s ++ s1) ++ [mup] ++ s2)) by (eexists; eauto).
eapply Hnc; eauto.
Qed.

Lemma nocom_wtR: forall p q q' s, nocom p q ->
  wt q s q' -> nocom p q'.
Proof.
unfold nocom; intros ? ? ? ? Hnc Hwt.
intros ? ? ? ? ? ? Hewp Hewq.
unfold ewt in Hewq.
destruct Hewq as [q'' Hq'].
set (lem:= WeakTransitions.wt_concat _ _ _ _ _ Hwt Hq'). 
replace (s ++ s1' ++ [muq] ++ s2') with 
  ((s ++ s1') ++ [muq] ++ s2') in lem by 
  (cbn; rewrite app_assoc; auto).
assert (ewt q ((s ++ s1') ++ [muq] ++ s2')) by (eexists; eauto).
eapply Hnc; eauto.
Qed.

Lemma nocom_lt: forall p q P, 
  lts (p‖q) Ltau P -> nocom p q ->
  (exists p', lts p Ltau p' /\ P=p'‖q) \/ 
  (exists q', lts q Ltau q'/\ P=p‖q')  .
Proof.
intros ? ? ? Hlt Hnc.
inversion Hlt; subst; eauto; 
assert (dual (Aout c v) (Ainp c v)) by (cbv; auto);  
apply exitst_wt in H1, H2;
replace [Aout c v] with ([]++[Aout c v]++[]) in H1 by auto; 
replace [Ainp c v] with ([]++[Ainp c v]++[]) in H2 by auto; 
try specialize (Hnc _ _ _ _ _ _ H1 H2); 
try specialize (Hnc _ _ _ _ _ _ H2 H1); exfalso; eauto.
Qed.

(*--------- forcing convergence ----------------------*)  


Lemma one_sided_cnv: forall p q,  
  q ⤓ -> p ↛ -> nocom p q -> (p‖q)⤓.
Proof.
intros ? ? Hqter; revert p.
dependent induction Hqter.
intros; constructor; intros ? Hlt.
set (lem:= nocom_lt _ _ _ Hlt H2).
destruct lem as [lem|lem].
- destruct lem as [p' [Hlt2 Heq]]; subst.
  exfalso; apply (ref_exf _ p') in H1; auto.
- destruct lem as [p' [Hlt2 Heq]]; subst. 
  specialize (H0 _ Hlt2 _ H1).
  eapply H0, nocom_ltR; eauto.
Qed.


Lemma forced_term: forall p q,   
  p⤓ -> q⤓ -> nocom p q -> 
  (p‖q)⤓.
Proof.
intros ? ? Hterp; revert q. 
dependent induction Hterp.
destruct (ltau_dec p); try apply ref_exf_rev in H1;  
eauto using one_sided_cnv.
intros ? Hterq Hnc.
constructor; intros P Hlt.
destruct (nocom_lt _ _ _ Hlt Hnc) as 
  [ [p2 [Hlt0 Heq]]| [q' [Hlt0 Heq]]]; subst.
+ specialize (H0 _ Hlt0 _ Hterq (nocom_ltL _ _ _ Hnc Hlt0)); auto.
+ dependent induction Hterq.
  constructor; intros ? Hlt2.
  set (lem:= nocom_ltR _ _ _  Hnc Hlt0).
  destruct (nocom_lt _ _ _ Hlt2 lem). 
  * destruct H4 as [pp [Hpp Heq]]; subst.
    assert (q' ⤓); eauto with mdb.
    specialize (H0 _ Hpp _ H4); apply H0.
    set (lemm:= nocom_ltL _ _ _  Hnc Hpp).
    set (lemmm:= nocom_ltR _ _ _  lemm Hlt0).
    auto.
  * destruct H4 as [pp [Hpp Heq]]; subst.
    specialize (H3 _ Hlt0).
    set (lemm:= nocom_ltR _ _ _  Hnc Hlt0).
    specialize (H3 lemm pp).
    assert (lts (p ‖ q') Ltau (p ‖ pp)); eauto with mdb.
Qed.
 
 

Lemma forced_cnv: forall s p q,
  (forall s1 s2, zip s s1 s2 -> p⇓s1 /\ q⇓s2) -> 
  nocom p q -> (p‖q)⇓s.
Proof.
intro s.
dependent induction s; intros ? ? Hzc Hnc.
- constructor; assert (zip [] [] []) by constructor.
  destruct (Hzc _ _ H) as [Hp Hq]; 
  inversion Hp; inversion Hq; 
  eauto using forced_term.
- specialize (IHs _ eq_refl JMeq_refl).
  constructor.
  + assert (zip (a :: s) [a] s) by (eapply zip_consL; eauto using zip_idR). 
    specialize (Hzc _ _ H); destruct Hzc as [Hp Hq].
    apply cnv_terminate in Hp,Hq; eauto using forced_term.
  + intros P Hwt.
    set (lem:= wt_invpar _ _ _ _ Hwt).
    destruct lem as [p' [q' Heq]]; subst.     
    assert (forall s1 s2, zip s s1 s2 → p⇓s1 ∧ q⇓s2).
    apply unzip_wt in Hwt.
    destruct Hwt as [s1 [s2 [Hzip [Hp Hq]]]].
    intros se sf Hzef.
    assert (p⇓a::se ∧ q⇓sf) by (apply Hzc; constructor; auto).
    assert (p⇓se ∧ q⇓a::sf) by (apply Hzc; constructor; auto).
    destruct H as [pase qsf]; destruct H0 as [pse qasf]; eauto.
    set (lem:= IHs _ _ H Hnc).
    apply unzip_wt in Hwt.
    destruct Hwt as [sp [sq [Hzip [Hp Hq]]]].
    inversion Hzip; subst.
    * assert (s1=[]). 
      inversion H4; subst; auto; unfold nocom in Hnc.
      exfalso; eapply Hnc; unfold ewt; try eexists; 
      replace (a :: mu1 :: s2) with ([a]++[mu1]++s2) in Hp;
      replace (mu2::s3) with ([]++[mu2]++s3) in Hq; eauto. 
      subst; inversion H4; subst.
      assert (forall s1 s2, zip s s1 s2 → p'⇓s1 ∧ q'⇓s2).
      intros se sf Hzef.
      assert (p⇓a::se ∧ q⇓sf) by (apply Hzc; constructor; auto).
      destruct H0 as [Hpase Hqsf]; split.
      eauto using cnv_preserved_by_wt_act.
      eauto using cnv_preserved_by_wt_nil.
      set (lem0:= nocom_wtL _ _ _ _ Hnc Hp). 
      set (lemm:= nocom_wtR _ _ _ _ lem0 Hq); auto.
    *  assert (s2=[]). 
      inversion H4; subst; auto; unfold nocom in Hnc.
      exfalso; eapply Hnc; unfold ewt; try eexists; 
      replace (mu1 :: s1) with ([]++[mu1]++s1) in Hp;
      replace (a::mu2::s3) with ([a]++[mu2]++s3) in Hq; eauto. 
      subst; inversion H4; subst.
      assert (forall s1 s2, zip s s1 s2 → p'⇓s1 ∧ q'⇓s2).
      intros se sf Hzef.
      assert (p⇓se ∧ q⇓a::sf) by (apply Hzc; constructor; auto).
      destruct H0 as [Hpse Hqasf]; split.
      eauto using cnv_preserved_by_wt_nil.
      eauto using cnv_preserved_by_wt_act.
      set (lem0:= nocom_wtL _ _ _ _ Hnc Hp). 
      set (lemm:= nocom_wtR _ _ _ _ lem0 Hq); auto.
    * unfold nocom in Hnc; exfalso; eapply Hnc; try eexists; 
         replace (wt p (mu1 :: s1) p') with 
           (wt p ([]++[mu1]++ s1) p') in Hp; 
         replace (wt q (mu2 :: s2) q') with 
           (wt q ([]++[mu2]++ s2) q') in Hq; eauto.
Qed.

  





(* attemps at coinductive stuff



CoInductive gtrace {A:Type} :=
| gnil
| gcons (x:A) (xs:gtrace)  .
Notation "x :: xs" := (gcons x xs).        
Notation "[]" := gnil.        



CoInductive tts: proc -> gtrace -> Prop :=
| tts_cons: forall p p' mu s, 
    lts p (ActExt mu) p' -> tts p' s -> tts p (mu:: s). 

CoInductive div: proc -> Prop :=
| div_gen: forall p p',
   lts p Ltau p' -> div p -> div p'
| div_parL: forall p q,
   div p -> div (p‖q)
| div_parR: forall p q,
   div q -> div (p‖q).
 

CoInductive cozip: gtrace -> gtrace -> gtrace -> Prop :=
| cozip_nil: cozip [] [] []
| cozip_consL: forall s s1 s2 mu,
    cozip s s1 s2 -> cozip (mu::s) (mu::s1) s2 
| cozip_consR: forall s s1 s2 mu,
    cozip s s1 s2 -> cozip (mu::s) s1 (mu::s2) 
| cozip_consLR: forall s s1 s2 mu1 mu2,
    cozip s s1 s2 -> dual mu1 mu2 -> 
    cozip s (mu1::s1) (mu2::s2) 
.

 


Lemma zip_lt: forall p q s1 s2, 
  cozip [] s1 s2 -> tts p s1 -> tts q s2 ->
  exists Q, lts (p‖q) Ltau Q.
Proof.
intros ? ? ? ? Hcoz Hp Hq.
inversion Hp; inversion Hq; inversion Hcoz; subst.
- inversion H8.
- inversion H10; inversion H11; subst.
  clear H10 H11. clear Hcoz.
  set (lem:= lts_com _ _ _ _ _ _ H H3 H8). 
  eexists. apply lem.
Qed.

*)


 



