import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfCoefficientsSeparatingCharactersEqZero

open MeasureTheory
open scoped Pointwise

namespace GlobalTheory.AverageConst

@[to_additive setIntegral_add_left]
theorem setIntegral_mul_left {Z : Type} [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z] [MeasurableSpace Z]
    [BorelSpace Z] (hc : ∀ a b : Z, a * b = b * a) (Λ : Subgroup Z) [Countable Λ] (μ : Measure Z)
    [μ.IsMulLeftInvariant] {F : Set Z} (hF : IsFundamentalDomain Λ F μ) (φ : Z → ℂ)
    (hφ : ∀ γ ∈ Λ, ∀ z, φ (γ * z) = φ z) (a : Z) : ∫ z in F, φ (a * z) ∂μ = ∫ z in F, φ z ∂μ := by
  have : SMulCommClass Z Λ Z := ⟨fun a γ z => by
    change a * ((γ : Z) * z) = (γ : Z) * (a * z)
    rw [← mul_assoc, hc a, mul_assoc]⟩
  rw [hF.setIntegral_eq (hF.smul_of_comm a) fun γ z => hφ γ γ.2 z]
  exact ((measurePreserving_mul_left μ a).setIntegral_image_emb (measurableEmbedding_mulLeft a) φ F).symm

theorem average_const {Y Z A : Type} [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [T2Space Y]
    [LocallyCompactSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (Γ : AddSubgroup Y)
    [DiscreteTopology Γ] {K : Set Y} (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ K) [AddCommGroup A] (χ : A → Y → ℂ)
    (h1 : ∀ a, Continuous (χ a)) (h2 : ∀ a x y, χ a (x + y) = χ a x * χ a y) (h3 : ∀ a b x, χ (a + b) x = χ a x * χ b x)
    (h4 : ∀ x, χ 0 x = 1) (h5 : ∀ a x, ‖χ a x‖ = 1) (h6 : ∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ)
    (ν : Measure Y) [ν.IsAddHaarMeasure] {G : Set Y} (hG : IsAddFundamentalDomain Γ G ν)
    [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z] [MeasurableSpace Z]
    [BorelSpace Z] (hc : ∀ a b : Z, a * b = b * a) (Λ : Subgroup Z) [Countable Λ] (μ : Measure Z)
    [μ.IsMulLeftInvariant] {F : Set Z} (hF : IsFundamentalDomain Λ F μ) (hfin : μ F ≠ ⊤)
    (k : Z → Y → ℂ) (kz : ∀ y, Continuous fun z => k z y) (ky : ∀ z, Continuous (k z)) {C : ℝ} (kb : ∀ z y, ‖k z y‖ ≤ C)
    (kΛ : ∀ γ ∈ Λ, ∀ z y, k (γ * z) y = k z y) (kΓ : ∀ γ ∈ Γ, ∀ z y, k z (γ + y) = k z y)
    (htw : ∀ a, (∀ y, χ a y = 1) ∨ ∃ (z₁ : Z) (c : ℂ), c ≠ 1 ∧
      ∀ z, ∫ y in G, χ a y * k (z₁ * z) y ∂ν = c * ∫ y in G, χ a y * k z y ∂ν) (y₀ : Y) :
    ∫ z in F, k z y₀ ∂μ = ∫ z in F, k z 0 ∂μ := by
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have : IsFiniteMeasure (ν.restrict G) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_addFundamentalDomain_lt_top_of_cocompact Γ hK hcov ν hG⟩
  have : IsFiniteMeasure (μ.restrict F) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Y → ℂ, ∀ y, Φ y = ∫ z in F, k z y ∂μ := ⟨_, fun _ => rfl⟩
  have hΦc : Continuous Φ := by
    rw [funext hΦ]
    exact continuous_of_dominated (bound := fun _ => C) (fun y => (kz y).aestronglyMeasurable)
      (fun y => .of_forall fun z => kb z y) (integrable_const _) (.of_forall ky)
  have hΦp : ∀ γ ∈ Γ, ∀ y, Φ (γ + y) = Φ y := fun γ hγ y => by simp only [hΦ, kΓ γ hγ]
  have hΦb : ∀ y, ‖Φ y‖ ≤ C * (μ.restrict F).real Set.univ := fun y => by
    rw [hΦ]; exact norm_integral_le_of_norm_le_const (.of_forall fun z => kb z y)
  have hint : ∀ a y₁, Integrable (fun y => χ a y * Φ (y₁ + y)) (ν.restrict G) := fun a y₁ =>
    Integrable.of_bound ((h1 a).mul (hΦc.comp (continuous_const.add continuous_id))).aestronglyMeasurable _
      (.of_forall fun y => by rw [norm_mul, h5, one_mul]; exact hΦb _)
  have hco : ∀ a, (∀ y, χ a y = 1) ∨ ∫ y in G, χ a y * Φ y ∂ν = 0 := fun a => (htw a).imp_right fun ⟨z₁, c, hc1, h⟩ => by
    have hm : StronglyMeasurable (Function.uncurry fun y z => χ a y * k z y) :=
      stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable (fun z => (h1 a).mul (ky z))
        fun y => (continuous_const.mul (kz y)).stronglyMeasurable
    have e : ∫ y in G, χ a y * Φ y ∂ν = ∫ z in F, ∫ y in G, χ a y * k z y ∂ν ∂μ := by
      simp only [hΦ, ← integral_const_mul]
      exact integral_integral_swap (Integrable.of_bound hm.aestronglyMeasurable C (.of_forall fun p => by
        rw [Function.uncurry, norm_mul, h5, one_mul]; exact kb _ _))
    have e2 := setIntegral_mul_left hc Λ μ hF (fun z => ∫ y in G, χ a y * k z y ∂ν)
      (fun γ hγ z => by simp only [kΛ γ hγ]) z₁
    simp only [h, integral_const_mul] at e2
    rw [e]
    exact (mul_left_eq_self₀.1 e2).resolve_left hc1
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero Y Γ K hK hcov A χ h1 h2 h3 h4 h5 h6 ν G
    inferInstance hG (fun y => Φ (y₀ + y) - Φ (0 + y))
    ((hΦc.comp (continuous_const.add continuous_id)).sub (hΦc.comp (continuous_const.add continuous_id)))
    (fun γ hγ y => by rw [add_left_comm, hΦp γ hγ, add_left_comm, hΦp γ hγ]) fun a => by
      have e := setIntegral_add_left add_comm Γ ν hG (fun y => χ a y * Φ y)
        (fun γ hγ y => by rw [h2, (h6 γ).2 hγ, one_mul, hΦp γ hγ]) y₀
      simp only [h2, mul_assoc, integral_const_mul] at e
      simp only [mul_sub]
      rw [integral_sub (hint a _) (hint a _), sub_eq_zero]
      simp only [zero_add]
      rcases hco a with h | h
      · rwa [h, one_mul] at e
      · rw [h] at e ⊢
        exact (mul_eq_zero.1 e).resolve_left fun h0 => by simpa [h0] using h5 a y₀
  have := congrFun key 0
  simp only [add_zero, Pi.zero_apply, sub_eq_zero] at this
  rw [← hΦ, ← hΦ, this]

end GlobalTheory.AverageConst
