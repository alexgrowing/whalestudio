import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenProd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem line_zero_const {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F (DegPre.zeroF D F)) (DegPre.lineε k))) (hw : w.IsGen) :
    ∃ c : Fˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (z : Z) (J), Good D.P.L z J →
      (val w r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c.val) := by
  have hI : IsIso (Scheme.Hom.appTop (𝟙 (TF (R := R) F).left)) :=
    inferInstanceAs (IsIso (Scheme.Hom.app (𝟙 (TF (R := R) F).left) ⊤))
  obtain ⟨a, ha⟩ := H1.exists_const D.P.L D.P.isLB (𝟙 _) (ConcreteCategory.bijective_of_isIso _).2 w hw
    (fun U _ h => by
      rw [Fin.prod_univ_two]
      show h (DegPre.zeroF D F).left ^ (k : ℤ) * h (DegPre.zeroF D F).left ^ (-(k : ℤ)) = 1
      rw [zpow_neg, mul_inv_cancel])
  obtain ⟨c, rfl⟩ : ∃ c : F, (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c = a :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 a
  have hc : c ≠ 0 := by
    rintro rfl
    let z : (TF (R := R) F).left := (⊥ : PrimeSpectrum F)
    choose I hI using fun χ : (TF (R := R) F).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
    have e := ha _ (𝟙 _) z I hI
    rw [gs_eq _ z ⊤ trivial, map_zero] at e
    exact (val w (𝟙 _) z I).ne_zero (e.trans ((congrArg _ (map_zero _)).trans (map_zero _)))
  refine ⟨Units.mk0 c hc, fun Z r z J hJ => ?_⟩
  have e := ha Z r z J hJ
  rw [Category.comp_id] at e
  exact e

theorem trPt_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] : DegPre.trPt D F (DegPre.zeroF D F) = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [DVR.tr_fst, Category.id_comp]
  · refine (DVR.tr_pr D F _).trans ?_
    have : fst (TF (R := R) F) D.P.A ≫ DegPre.zeroF D F = 1 := MonObj.comp_one (M := D.P.A) _
    rw [this, _root_.mul_one, Category.id_comp]

theorem phiRaw_torus : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (g : GtPtF D F) (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k))), g.b = DegPre.zeroF D F → w.IsGen → ∃ c : Fˣ, ∀ s s' : Raw D F k, PhiRaw D F k 0 g w s s' → (∀ α, (∃ j, (s α).f j ≠ 0) → ∀ z J, Good D.P.L z J → val (g.s α) (𝟙 _) z J = 1) → ∀ α j, (s' α).f j = DegPre.constBF D F c.val _ * (s α).f j := by
  intro R _ _ D F _ _ k g w hb hw
  obtain ⟨b, gs', hg, h0, hm⟩ := g
  dsimp only at hb w
  subst hb
  obtain ⟨c, hc⟩ := line_zero_const D F k w hw
  refine ⟨c, fun s s' H hs α j => ?_⟩
  obtain ⟨u, hu, vu⟩ := exists_gen D.P.isLB (φ' := DegPre.phiφ D F 0 α (DegPre.zeroF D F)) (ε' := DegPre.deltaε k)
    (fun U _ h => by
      have e₁ : padd D.P.A (DegPre.cF D F α) (DegPre.zeroF D F) = DegPre.cF D F α :=
        _root_.mul_one (DegPre.cF D F α)
      rw [DegPre.phiφ, trPt_zero, add_zero]
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 2) (U := U) _ (c := 1) (c' := 1) ?_ ?_)
        (Eq.trans ?_ (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _
          (c := ∏ i, h (DegPre.famφ D F α i) ^ DegPre.famε k i) rfl
          (DVR.prod_neg _ _ (c := ∏ i, h (DegPre.famφ D F α i) ^ DegPre.famε k i) ?_)).symm)
      · simp [Fin.prod_univ_four, DegPre.gtφ, DegPre.gtε, e₁]
      · simp [Fin.prod_univ_two, DegPre.lineφ, DegPre.lineε]
      · simp
      · simp)
    (LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (gs' α) w) (fst (TF (R := R) F) D.P.A).left)
    (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (hg α) hw) _)
  have z₁ : (DegPre.zF D F).left ≫ (fst (TF (R := R) F) D.P.A).left = 𝟙 _ :=
    congrArg (fun q => q.left) (lift_fst (𝟙 (TF (R := R) F)) (toUnit _ ≫ η[D.P.A]))
  have rel := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (H α u hu (corr_of_val D.P.isLB fun y J hJ => by
    rw [val_pull hJ, vu _ _ y J hJ, val_pull hJ, Category.id_comp, z₁]))
  have key : ∀ y J, Good D.P.L y J → sval (s' α) (𝟙 _) y J = sval (s α) (𝟙 _) y J *
      ((val (gs' α) (fst (TF (R := R) F) D.P.A).left y J).val *
        gs (fst (TF (R := R) F) D.P.A).left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c.val)) := by
    intro y J hJ
    have e := rel _ (𝟙 _) y J hJ
    rw [vu _ _ y J hJ, val_pull hJ, val_mul hJ, Category.id_comp, Category.id_comp, Units.val_mul, hc _ _ y J hJ] at e
    dsimp only at e
    rw [trPt_zero, add_zero] at e
    exact e
  refine fn_ext fun y hy => ?_
  choose I hI using fun χ : (DegPre.BF D F).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ y)
  have hI' : Good D.P.L y I := hI
  have e₁ := sec_trans (s' α) (𝟙 _) y hy (hI'.mem _ (𝟙 _))
  have e₂ := sec_trans (s α) (𝟙 _) y hy (hI'.mem _ (𝟙 _))
  have e₃ : gs (𝟙 _) y _ (DegPre.constBF D F c.val _ * (s α).f j) =
      gs (𝟙 _ ≫ (fst (TF (R := R) F) D.P.A).left) y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c.val) *
        gs (𝟙 _) y (LB.wchart D.P.L (DegPre.famφ D F α) j) ((s α).f j) :=
    (gs_mul (𝟙 _) y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_res (𝟙 _) y le_top hy _).trans
      (gs_pull (𝟙 _) (fst (TF (R := R) F) D.P.A).left y ⊤ trivial _)) rfl)
  rw [Category.id_comp] at e₃
  have e₄ : sval (s α) (𝟙 _) y I * (val (gs' α) (fst (TF (R := R) F) D.P.A).left y I).val = sval (s α) (𝟙 _) y I := by
    by_cases hz : ∃ j, (s α).f j ≠ 0
    · have hcorr : LB.Gen.Corr D.P.L _ _ _ _ (gs' α) (LB.oneGen D.P.L) :=
        corr_of_val D.P.isLB fun z J hJ => (hs α hz z J hJ).trans (val_one _).symm
      rw [val_corr hI' hcorr, val_one, Units.val_one, _root_.mul_one]
    · push_neg at hz
      have : sval (s α) (𝟙 _) y I = 0 :=
        (congrArg (gs (𝟙 _) y _) (hz _)).trans ((gs_eq _ y _ (hI'.mem _ (𝟙 _)) _).trans
          ((congrArg _ (map_zero _)).trans (map_zero _)))
      rw [this, MulZeroClass.zero_mul]
  have e₅ := key y I hI'
  rw [← _root_.mul_assoc, e₄] at e₅
  refine e₁.trans (Eq.trans ?_ (e₃.trans (congrArg _ e₂)).symm)
  refine (congrArg _ e₅).trans ?_
  rw [sval]; ring

end GlobalTheory.UU
