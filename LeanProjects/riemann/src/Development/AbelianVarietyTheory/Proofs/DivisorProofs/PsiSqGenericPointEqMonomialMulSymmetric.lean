import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic
noncomputable section

namespace GlobalTheory.PsiSqGeneric

theorem jFK_self (V : Type) [CommRing V] [IsDomain V] :
    jFK (R := V) (FractionRing V) = 𝟙 (Spec (CommRingCat.of (FractionRing V))) := by
  show Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (FractionRing V))) = 𝟙 _
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

theorem cst_eq_gm {V : Type} [CommRing V] [IsDomain V] (z : Spec (CommRingCat.of (FractionRing V)))
    (k : (FractionRing V)ˣ) :
    cst (R := V) (FractionRing V) z (k : FractionRing V) =
      (gm (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z ⊤ (unitOn k)).val := by
  rw [← gs_unit _ z ⊤ trivial]
  rfl

end GlobalTheory.PsiSqGeneric

namespace GlobalTheory.PsiSqGeneric

theorem core (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (hE : D.PsiEven)
    (h0 : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TK V).left) (z : Z) J, Good D.P.L z J →
      val (D.psi 0) r z J * val D.rigK r z J = 1)
    (τ₀ : GlobalTheory.UChart.Gens D) (N : ℕ) (s : Fin N → V) (ε : Fin N → LinearMap.BilinForm ℤ D.X)
    (hT : GlobalTheory.UChart.TauIn D τ₀ s ε) (mu : D.X) : ∃ k : (FractionRing V)ˣ,
      (k : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ε i mu mu ∧
      ∀ (z : Spec (CommRingCat.of (FractionRing V)))
        (J : (Spec (CommRingCat.of (FractionRing V)) ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
        (val (D.psi mu) (jFK (R := V) (FractionRing V)) z J).val ^ 2 =
          cst (R := V) (FractionRing V) z (k : FractionRing V) *
            (val D.sym ((toUnit (TF (R := V) (FractionRing V))).left ≫ (D.c mu).left) z J *
              (val (τ₀ mu (-mu)) (toUnit (TF (R := V) (FractionRing V))).left z J)⁻¹ *
              (rigV D (toUnit (TF (R := V) (FractionRing V))).left z J ^ 2)⁻¹).val := by
  obtain ⟨-, k', hk', hv⟩ := hT mu (-mu)
  refine ⟨k'⁻¹, ?_, fun z J hJ => ?_⟩
  · rw [Units.val_inv_eq_inv_val, hk']
    simp only [map_neg, zpow_neg, Finset.prod_inv_distrib, inv_inv]
  · have hv' : val (D.tau mu (-mu)) (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z J =
        gm (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z ⊤ (unitOn k') * val (τ₀ mu (-mu)) (jK V) z J :=
      hv z J hJ
    have ev := val_corr hJ (hE mu) (𝟙 (Spec (CommRingCat.of (FractionRing V))))
    rw [val_mul hJ, val_pull hJ, Category.id_comp] at ev
    have p0 := h0 _ (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z J hJ
    have hrig : val D.rigK (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z J = rigV D (jK V) z J := by
      rw [DegPre.rigK, val_pull hJ, Category.id_comp]; rfl
    have hx : D.xK mu = jK V ≫ (D.c mu).left := rfl
    unfold DegPre.tau at hv'
    rw [val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_inv,
      congrArg (fun w => val (D.psi w) (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z J) (add_neg_cancel mu)] at hv'
    rw [hx] at ev
    rw [hrig] at p0 hv'
    rw [jFK_self, GlobalTheory.Poinc.Sep.Frames.toUnit_left_eq, cst_eq_gm]
    have hg : gm (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z ⊤ (unitOn k'⁻¹) =
        (gm (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z ⊤ (unitOn k'))⁻¹ := by
      rw [← map_inv]; rfl
    rw [hg, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
    congr 1
    have hp := eq_inv_of_mul_eq_one_left p0
    have hb := eq_mul_inv_of_mul_eq ev
    have hG := eq_mul_inv_of_mul_eq hv'.symm
    rw [hG, hp, hb]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    abel

end GlobalTheory.PsiSqGeneric

theorem GlobalTheory.PsiSqGeneric.main : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), D.PsiEven →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ (TK V).left) (z : Z) J, Good D.P.L z J →
      val (D.psi 0) r z J * val D.rigK r z J = 1) →
    ∀ (τ₀ : GlobalTheory.UChart.Gens D) (N : ℕ) (s : Fin N → V) (ε : Fin N → LinearMap.BilinForm ℤ D.X),
    GlobalTheory.UChart.TauIn D τ₀ s ε → ∀ mu : D.X, ∃ k : (FractionRing V)ˣ,
      (k : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ε i mu mu ∧
      ∀ z J, Good D.P.L z J →
        (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (D.psi mu) (jFK (R := V) (FractionRing V)) z J)).val ^ 2 =
          cst (FractionRing V) z (k : FractionRing V) *
            (val D.sym ((toUnit (TF (R := V) (FractionRing V))).left ≫ (D.c mu).left) z J *
              (val (τ₀ mu (-mu)) (toUnit (TF (R := V) (FractionRing V))).left z J)⁻¹ *
              (rigV D (toUnit (TF (R := V) (FractionRing V))).left z J ^ 2)⁻¹).val := by
  intro V _ _ D hE h0 τ₀ N s ε hT mu
  exact GlobalTheory.PsiSqGeneric.core V D hE h0 τ₀ N s ε hT mu
