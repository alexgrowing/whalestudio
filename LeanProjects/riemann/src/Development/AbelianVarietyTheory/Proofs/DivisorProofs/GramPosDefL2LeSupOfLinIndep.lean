import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramIsHermitianL2EqDoubleSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramPosDefOfL2DefiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousHermSectionValueMulConjAndNormBoundedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVolumeDensityFiniteIsOpenPosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentComplexSectionValuesOfIntStatement
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
open scoped ComplexOrder
namespace GlobalTheory.HSAmp

theorem gram_posDef_and_l2_le_sup_bound : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p) (ω : ∀ σ, VolDens p σ D) (a b : ℤ) (ι : Type) [Fintype ι] [DecidableEq ι] (f : ι → X.functionField), (∀ i, f i ∈ P.H a b) → LinearIndependent ℤ f → IsFam (fun σ => (ω σ).meas) (vals P a b f) ∧ (gram (fun σ => (ω σ).meas) (vals P a b f)).PosDef ∧ ∀ (c : ι → ℂ) (M : ℝ), (∀ σ y, cmb (vals P a b f) c σ y ≤ M) → l2 (fun σ => (ω σ).meas) (vals P a b f) c ≤ (∑ᶠ σ, ((ω σ).meas Set.univ).toReal) * M := by
  intro k _ X _ p D hX hG P ω a b ι _ _ f hf hli
  haveI : Finite (k →+* ℂ) := hX.finite_emb
  have hfin := fun σ => GlobalTheory.T.smoothVolumeDensity_finite_isOpenPos k X p D hX hG σ (ω σ)
  obtain ⟨hprod, hnu⟩ := GlobalTheory.T.continuous_hermSectionValue_mul_conj_and_norm_bounded k X p D hX P a b
  have hfam : IsFam (fun σ => (ω σ).meas) (vals P a b f) := by
    refine ⟨inferInstance, fun σ i j => ?_⟩
    haveI := (hfin σ).1
    obtain ⟨C₁, hC₁⟩ := (hnu (f i) (hf i)).2
    obtain ⟨C₂, hC₂⟩ := (hnu (f j) (hf j)).2
    refine Integrable.of_bound (hprod σ _ (hf i) _ (hf j)).aestronglyMeasurable (C₁ * C₂)
      (Filter.Eventually.of_forall fun y => ?_)
    have h0 : 0 ≤ P.nu a b σ y (f j) := (norm_val P a b σ y (f j)) ▸ norm_nonneg _
    simp only [vals, norm_mul, Complex.norm_conj, norm_val]
    exact mul_le_mul (hC₁ σ y) (hC₂ σ y) h0 (le_trans ((norm_val P a b σ y (f i)) ▸ norm_nonneg _) (hC₁ σ y))
  have hl2 := gram_isHermitian_and_l2_eq_quadratic_form (S := k →+* ℂ) (Y := fun σ => CxPts p σ) (ι := ι) (fun σ => (ω σ).meas) (vals P a b f) hfam
  have hcont : ∀ (c : ι → ℂ) σ, Continuous (cmb (vals P a b f) c σ) := by
    intro c σ
    have e : cmb (vals P a b f) c σ = fun y => (∑ i, ∑ j, (c i * (starRingEnd ℂ) (c j)) *
        (vals P a b f σ y i * (starRingEnd ℂ) (vals P a b f σ y j))).re := by
      funext y
      have h1 := Complex.mul_conj' (∑ i, c i * vals P a b f σ y i)
      rw [map_sum, Finset.sum_mul_sum] at h1
      simp only [cmb]
      rw [← Complex.ofReal_re (‖_‖ ^ 2), Complex.ofReal_pow, ← h1]
      congr 1
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [map_mul]; ring
    rw [e]
    exact Complex.continuous_re.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      continuous_const.mul (hprod σ _ (hf i) _ (hf j)))
  haveI : Fintype (k →+* ℂ) := Fintype.ofFinite _
  refine ⟨hfam, GlobalTheory.T.gram_posDef_of_l2_definite (k →+* ℂ) (fun σ => CxPts p σ) ι (fun σ => (ω σ).meas) (vals P a b f) hfam
    fun c hc => ?_, fun c M hM => ?_⟩
  · rw [l2, finsum_eq_sum_of_fintype] at hc
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun σ _ =>
      integral_nonneg fun y => sq_nonneg ‖∑ i, c i * vals P a b f σ y i‖).1 hc
    refine GlobalTheory.T.linearIndependent_complex_sectionValues_of_int k X p D hX P a b ι f hf hli c fun σ y => ?_
    haveI := (hfin σ).2
    have hae := (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg ‖∑ i, c i * vals P a b f σ y i‖)
      ((hl2.2 c).1 σ)).1 (hz σ (Finset.mem_univ _))
    have hall := (Continuous.ae_eq_iff_eq _ (hcont c σ) continuous_const).1 hae
    have hy : ‖∑ i, c i * vals P a b f σ y i‖ ^ 2 = 0 := congrFun hall y
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hy)
  · rw [l2, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.sum_mul]
    refine Finset.sum_le_sum fun σ _ => ?_
    haveI := (hfin σ).1
    calc ∫ y, cmb (vals P a b f) c σ y ∂(ω σ).meas ≤ ∫ _y, M ∂(ω σ).meas :=
          integral_mono ((hl2.2 c).1 σ) (integrable_const M) fun y => hM σ y
      _ = ((ω σ).meas Set.univ).toReal * M := by
          rw [integral_const, smul_eq_mul, measureReal_def]

end GlobalTheory.HSAmp
