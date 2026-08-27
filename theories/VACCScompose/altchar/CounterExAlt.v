
Require Import AltGenerality.






Lemma acep1: (g 𝟘) ≼ₐₛ tau (g 𝟘). 
Proof.
split.
- intros ? Hcnv.
  destruct s; try do 2 econstructor.
  * intros ? H; inversion H; constructor; 
    intros ? Hexf; inversion Hexf.
  * econstructor. 
    econstructor; intros ? H; inversion H; constructor; 
    intros ? Hexf; inversion Hexf.
    intros ? Hwt; inversion Hwt; inversion l; subst; 
    inversion w; subst; inversion l0.
- intros ? Q Hcnv Hwt Href.
  destruct s.
  * exists (g 𝟘); repeat split; eauto with mdb.
    intro amu. intro H.
    destruct H as [mu [H1 H2]]; destruct H1 as [mu0 [G1 [G2 G3]]].    
    apply inv_nonmublock in G1; destruct G1 as [q [Hexf| Hexf]]; inversion Hexf.
  * inversion Hwt; inversion l; subst; inversion w; inversion l0.
Qed.







Lemma acep2: forall x v,
  ~ sum 𝟘 (gtau (out x v)) ≼₂ sum (gtau (g 𝟘)) (gtau (out x v)). 
Proof.
intros ? ? Hlac; unfold "≼₂" in Hlac.
specialize (Hlac nil); specialize (Hlac (g 𝟘)). 
assert (sum 𝟘 (gtau (out x v)) ⇓ []).
{ do 2 constructor; intros ? Hlt; inversion Hlt; inversion H3;
  constructor; intros ? Hexf; inversion Hexf.
} assert (wt (sum (gtau 𝟘) (gtau (out x v))) [] 𝟘) by repeat econstructor.
assert ((g 𝟘) ↛) by set_solver. 
specialize (Hlac H H0 H1); clear H H0 H1.
destruct Hlac as [P [Hwt [Href Hsub]]].
inversion Hwt; subst.
+ assert (exists Q, lts (sum 𝟘 (gtau (out x v))) Ltau  Q) by eauto with mdb.
  apply inv_nonblock_rev in H; set_solver.
+ inversion l; inversion H3; subst.
  inversion w; try inversion l0; subst.
  assert ((exists mu, mu∈(Subset_Act.coR (g 𝟘)) )-> False).
  { intro Hexf; destruct Hexf as [mu Hexf]; destruct Hexf as [mu0 [G _]].
    apply inv_nonmublock in G; destruct G as [q [Hexf| Hexf]]; inversion Hexf.
  } 
  assert ( (exists pmu, pmu∈Alpha (Subset_Act.coR (g 𝟘)) )-> False).
  { intro Hexf; destruct Hexf as [pmu Hexf]; 
    destruct Hexf as [mu [Hexf _]]; eauto.
  }
  assert ( (Ainp x v)∈ (Subset_Act.coR (out x v))).
  { eexists (Aout x v); repeat split; eauto.   
    apply inv_nonmublock_rev; eauto with mdb.
    cbn; intro; inversion H1; inversion H2.
  }
  assert (alpha (Ainp x v) ∈ 
          Alpha (Subset_Act.coR (out x v))).
  by eexists; split; eauto. 
  set_solver.
Qed.
