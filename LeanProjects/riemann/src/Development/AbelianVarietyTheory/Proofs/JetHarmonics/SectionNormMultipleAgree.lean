import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HasFinOrderIff
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecLinIffComb
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HasGenPull
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsUniquePullExpands
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalisedPullbackSectionExpandsFamily
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GeneratorsCompare

namespace GlobalTheory.RigPullExp

theorem val_rigT {S Z : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (rig : LB.Gen (L.pull (eSec A)))
    (T : Over S) (k : ℤ) (r : Z ⟶ T.left) (z : Z) {J} (hJ : Good L z J) :
    val (rigT A L rig T k) r z J = val (L := L) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rig (r ≫ T.hom) z J ^ k := by
  have hm := hJ.mem (fun _ : Fin 1 => T.hom ≫ eSec A) r
  rw [val_of rig (r ≫ T.hom) z J (fun _ => J (r ≫ T.hom ≫ eSec A)) (fun _ => by rw [Category.assoc])]
  exact (map_zpow _ _ _).trans (congrArg (· ^ k) ((gm_res r z _ hm _).trans
    (gm_pull r T.hom z _ (rigT_le A L _ hm) _)))

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]
  (F : Type) [Field F] [Algebra (FractionRing V) F]

theorem surj_GF (hG : GlobalFnsSt) (U : UnifPre (maximalIdeal V) D A G) :
    Function.Surjective (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left.appTop.hom := by
  have e : (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left =
      (TFK (R := V) F ◁ U.gen.hom).left ≫ (fst (TFK (R := V) F) A.A).left := by
    rw [← Over.comp_left, whiskerLeft_fst]
  rw [e]
  refine surj_comp ?_ (surj_fst hG A.isAb _)
  have h2 : ((TFK (R := V) F ◁ U.gen.hom).left ≫ (TFK (R := V) F ◁ U.gen.inv).left).appTop =
      Scheme.Hom.appTop (𝟙 _) := by
    rw [← Over.comp_left, ← MonoidalCategory.whiskerLeft_comp, U.gen.hom_inv_id, MonoidalCategory.whiskerLeft_id]
    rfl
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] at h2
  intro a
  refine ⟨(TFK (R := V) F ◁ U.gen.inv).left.appTop.hom a, ?_⟩
  have h3 := congrArg (fun f => f.hom a) h2
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply] using h3

theorem cmp_fst : RigidNormaliserGenerators.cmp G F ≫ (fst (TF (R := V) F) G).left =
    (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left :=
  pullback.lift_fst _ _ _

theorem snd_endK (φ : G ⟶ G) : (snd (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left ≫ endK φ ≫ gK =
    RigidNormaliserGenerators.cmp G F ≫ (snd (TF (R := V) F) G ≫ φ).left := by
  have he : endK φ ≫ gK = gK ≫ φ.left := pullback.lift_fst _ _ _
  rw [Over.comp_left, ← Category.assoc (RigidNormaliserGenerators.cmp G F), RigidNormaliserGenerators.cmp_snd, he]
  exact (Category.assoc _ _ _).symm

theorem cmp_whisker (φ : G ⟶ G) :
    ((TFK (R := V) F) ◁ (Over.pullback (jK V)).map φ).left ≫ RigidNormaliserGenerators.cmp G F =
      RigidNormaliserGenerators.cmp G F ≫ (TF (R := V) F ◁ φ).left := by
  refine pullback.hom_ext (f := (TF (R := V) F).hom) (g := G.hom) ?_ ?_
  · change (_ ≫ _) ≫ (fst (TF (R := V) F) G).left = (_ ≫ _) ≫ (fst (TF (R := V) F) G).left
    rw [Category.assoc, Category.assoc, cmp_fst, ← Over.comp_left, ← Over.comp_left, whiskerLeft_fst,
      whiskerLeft_fst, cmp_fst]
  · change (_ ≫ _) ≫ (snd (TF (R := V) F) G).left = (_ ≫ _) ≫ (snd (TF (R := V) F) G).left
    rw [Category.assoc, Category.assoc, RigidNormaliserGenerators.cmp_snd, ← Over.comp_left, whiskerLeft_snd, ← snd_endK,
      UnifPre.gFK, ← Category.assoc, ← Over.comp_left, whiskerLeft_snd, Over.comp_left, Category.assoc]
    rfl

theorem gen_eq (hG : GlobalFnsSt) (U : UnifPre (maximalIdeal V) D A G) (φ : G ⟶ G) (k N : ℕ) (hN : 0 < N)
    (u : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![gK, endK φ ≫ gK] ![((k * N : ℕ) : ℤ), -(k : ℤ)])) (hu : u.IsGen)
    (hc : LB.Gen.Corr U.LG.L _ _ _ _ (LB.pullGen U.LG.L _ _ u unitK)
      (LB.pullGen U.LG.L _ _ (GeneratorPullback.powGen U.LG.L _ _ U.LG.rig (k * (N - 1))) (jK V)))
    (α : LB.Gen (LB.LinComb U.LG.L (K := Fin 2)
      ![(snd (TF (R := V) F) G).left, (snd (TF (R := V) F) G ≫ φ).left] ![((k * N : ℕ) : ℤ), -(k : ℤ)]))
    (hα : α.IsGen)
    (hc' : LB.Gen.Corr U.LG.L _ _ _ _ (LB.pullGen U.LG.L _ _ α (ptSecT G (1 : TF (R := V) F ⟶ G)).left)
      (rigT G U.LG.L U.LG.rig (TF (R := V) F) (((k * N : ℕ) : ℤ) - k)))
    (y : (UnifPre.GF (G := G) F).left) (J) (hJ : Good U.LG.L y J) :
    val α (RigidNormaliserGenerators.cmp G F) y J = val u (snd (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left y J := by
  have hL := U.LG.isLB
  obtain ⟨e, e₁, e₂⟩ : ∃ e : Spec (CommRingCat.of F) ⟶ (UnifPre.GF (G := G) F).left,
      e ≫ (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left = 𝟙 _ ∧
      e ≫ (snd (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left = jFK (R := V) F ≫ unitK :=
    ⟨pullback.lift (f := jFK (R := V) F) (g := pullback.snd G.hom (jK V)) (𝟙 _) (jFK (R := V) F ≫ unitK) (by
      have : unitK ≫ pullback.snd G.hom (jK V) = 𝟙 _ := pullback.lift_snd _ _ _
      rw [Category.assoc, this, Category.id_comp]
      exact (Category.comp_id _).symm), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have e₃ : e ≫ RigidNormaliserGenerators.cmp G F = (ptSecT G (1 : TF (R := V) F ⟶ G)).left := by
    refine pullback.hom_ext (f := (TF (R := V) F).hom) (g := G.hom) ?_ ?_
    · change (_ ≫ _) ≫ (fst (TF (R := V) F) G).left = _ ≫ (fst (TF (R := V) F) G).left
      rw [Category.assoc, cmp_fst, e₁, ← Over.comp_left, ptSecT, lift_fst]
      rfl
    · change (_ ≫ _) ≫ (snd (TF (R := V) F) G).left = _ ≫ (snd (TF (R := V) F) G).left
      have hu : unitK ≫ (gK : pullback G.hom (jK V) ⟶ G.left) = jK V ≫ eSec G := pullback.lift_fst _ _ _
      rw [Category.assoc, RigidNormaliserGenerators.cmp_snd, ← Over.comp_left, ptSecT, lift_snd, UnifPre.gFK, ← Category.assoc, e₂]
      exact (Category.assoc _ _ _).trans ((congrArg (jFK (R := V) F ≫ ·) hu).trans (Category.assoc _ _ _).symm)
  have key := gen_unique' hL (u := LB.pullGen U.LG.L _ _ α (RigidNormaliserGenerators.cmp G F))
    (u' := LB.pullGen U.LG.L _ _ u (snd (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left)
    (fun W _ h => by
      rw [Fin.prod_univ_two, Fin.prod_univ_two]
      exact congrArg₂ (fun p q => h p ^ ((k * N : ℕ) : ℤ) * h q ^ (-(k : ℤ))) (RigidNormaliserGenerators.cmp_snd G F).symm
        (snd_endK F φ))
    _ e e₁ (surj_GF F hG U) (pullGen_isGen_of_isGen _ _ _ hα _) (pullGen_isGen_of_isGen _ _ _ hu _) (fun z I hI => by
      have c₁ := val_corr hI hc' (𝟙 _)
      have c₂ := val_corr hI hc (jFK (R := V) F)
      rw [val_pull hI, val_rigT _ _ _ _ _ hI, Category.id_comp, Category.id_comp] at c₁
      rw [val_pull hI, val_pull hI, val_pow] at c₂
      rw [val_pull hI, val_pull hI, e₃, e₂]
      refine c₁.trans (Eq.trans ?_ c₂.symm)
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
      rw [← zpow_natCast, show ((k * n.succ : ℕ) : ℤ) - k = ((k * (n.succ - 1) : ℕ) : ℤ) by
        rw [Nat.succ_sub_one]; push_cast; ring]
      rfl) _ (𝟙 _) y J hJ
  rwa [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp] at key

end

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (F : Type) [Field F] [Algebra (FractionRing V) F], letI := H.starRing; ∀ (a : 𝓞 E) (N : ℕ), a * star a = (N : 𝓞 E) → 0 < N → ∀ (k : ℕ), 1 ≤ k → ∀ (σ : LB.Sec (LPow t.G P.U.LG.L (k : ℤ) (TF (R := V) F))) (σ' : P.U.toUnifPre.SecGF F k) (s : Fam P.D.toPre F k) (σ₁ : LB.Sec (LPow t.G P.U.LG.L ((k * N : ℕ) : ℤ) (TF (R := V) F))) (σ₁' : P.U.toUnifPre.SecGF F (k * N)), RigidNormaliserGenerators.SameSec F P.U.toUnifPre k σ σ' → P.U.toUnifPre.ExpandsG F k σ' s → RigidNormaliserGenerators.IsRigPull t.G P.U.LG (t.act.act a) (k : ℤ) ((k * N : ℕ) : ℤ) σ σ₁ → RigidNormaliserGenerators.SameSec F P.U.toUnifPre (k * N) σ₁ σ₁' → ∃ s₁ : Fam P.D.toPre F (k * N), PullAl P.D F P.oD a k N s s₁ ∧ P.U.toUnifPre.ExpandsG F (k * N) σ₁' s₁ := by
  intro V _ _ _ E _ _ _ H t P F _ _ a N hN hN0 k hk σ σ' s σ₁ σ₁' hσ hs hp hσ₁
  letI := H.starRing
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨u, hu, hc⟩ := GlobalTheory.PullGenG.main hL.globalFns V E H t P a N hN hN0 k
  obtain ⟨α, hα, hc', htw⟩ := hp
  refine GlobalTheory.PullExpField.of_generic hL P.U P.oD a (t.act.act a) k N hk
    (GlobalTheory.PullEveryLevel.expands_pull_every_level hL P a N hN hN0 hk) u hu hc F σ' s hs σ₁' fun y J hJ => ?_
  rw [← SectionScalarValuation.secScal_sval hσ₁ _ y hJ, ← SectionScalarValuation.secScal_sval hσ _ y hJ, Category.id_comp,
    GlobalTheory.NormPullExp.twist_val htw _ y hJ, cmp_whisker,
    gen_eq F hL.globalFns P.U.toUnifPre (t.act.act a) k N hN0 u hu hc α hα hc' y J hJ]
  exact mul_comm _ _

end GlobalTheory.RigPullExp
