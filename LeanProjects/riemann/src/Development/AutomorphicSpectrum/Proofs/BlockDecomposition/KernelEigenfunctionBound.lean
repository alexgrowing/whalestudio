import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLLocalComponentIsUnitaris

open scoped ENNReal NNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.Conc.BesselPt

theorem sq_tsum_le {ι : Type*} (t : ι → ℝ≥0) (k : ℕ) (h : (Function.support t).encard ≤ k) :
    (∑' i, (t i : ℝ≥0∞)) ^ 2 ≤ k * ∑' i, (t i : ℝ≥0∞) ^ 2 := by
  have hfin : (Function.support t).Finite := Set.finite_of_encard_le_coe h
  set S := hfin.toFinset with hS
  have hcard : S.card ≤ k := by
    have : (S.card : ℕ∞) ≤ k := by
      rw [← Set.encard_coe_eq_coe_finsetCard, hS, hfin.coe_toFinset]; exact h
    exact_mod_cast this
  have hz : ∀ i, i ∉ S → t i = 0 := fun i hi => by simpa [hS] using hi
  have e1 : ∑' i, (t i : ℝ≥0∞) = ∑ i ∈ S, (t i : ℝ≥0∞) :=
    tsum_eq_sum (fun i hi => by simp [hz i hi])
  have e2 : ∑' i, (t i : ℝ≥0∞) ^ 2 = ∑ i ∈ S, (t i : ℝ≥0∞) ^ 2 :=
    tsum_eq_sum (fun i hi => by simp [hz i hi])
  rw [e1, e2]
  have h3 : (∑ i ∈ S, t i) ^ 2 ≤ k * ∑ i ∈ S, t i ^ 2 := by
    have h4 : ((∑ i ∈ S, (t i : ℝ)) ^ 2) ≤ S.card * ∑ i ∈ S, (t i : ℝ) ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have h5 : (∑ i ∈ S, t i) ^ 2 ≤ S.card * ∑ i ∈ S, t i ^ 2 := by exact_mod_cast h4
    exact h5.trans (by gcongr)
  exact_mod_cast h3

theorem sq_lintegral_mul_le {X : Type*} [MeasurableSpace X] (ν : Measure X) {f g : X → ℝ≥0∞}
    (hf : AEMeasurable f ν) (hg : AEMeasurable g ν) :
    (∫⁻ a, f a * g a ∂ν) ^ 2 ≤ (∫⁻ a, f a ^ 2 ∂ν) * ∫⁻ a, g a ^ 2 ∂ν := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two hf hg
  simp only [Pi.mul_apply, ENNReal.rpow_ofNat] at h
  refine (pow_le_pow_left' h 2).trans (le_of_eq ?_)
  rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (_ ^ _), ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul]
  norm_num

theorem encard_support_le {G : Type*} [Group G] [TopologicalSpace G] (Γ : Subgroup G) (α : G → ℂ) (x w : G)
    (k : ℕ)
    (hk : {γ : G | γ ∈ Γ ∧ ∃ a ∈ tsupport α, ∃ b ∈ tsupport α, γ = x * a * b⁻¹ * x⁻¹}.encard ≤ k) :
    (Function.support fun γ : Γ => ‖α (x⁻¹ * ((γ : G) * w))‖₊).encard ≤ k := by
  rcases (Function.support fun γ : Γ => ‖α (x⁻¹ * ((γ : G) * w))‖₊).eq_empty_or_nonempty with h0 | ⟨γ₀, h₀⟩
  · simp [h0]
  refine le_trans ?_ hk
  have hinj : Set.InjOn (fun γ : Γ => (γ : G) * (γ₀ : G)⁻¹)
      (Function.support fun γ : Γ => ‖α (x⁻¹ * ((γ : G) * w))‖₊) := by
    intro a _ b _ hab
    exact Subtype.ext (mul_right_cancel hab)
  rw [← hinj.encard_image]
  refine Set.encard_le_encard ?_
  rintro _ ⟨γ, hγ, rfl⟩
  have mem : ∀ c : Γ, c ∈ (Function.support fun γ : Γ => ‖α (x⁻¹ * ((γ : G) * w))‖₊) →
      x⁻¹ * ((c : G) * w) ∈ tsupport α := fun c hc => by
    apply subset_tsupport
    simpa [Function.mem_support] using hc
  refine ⟨Γ.mul_mem γ.2 (Γ.inv_mem γ₀.2), _, mem γ hγ, _, mem γ₀ h₀, ?_⟩
  group

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

theorem sq_lintegral_le (μ : Measure G) [μ.IsMulLeftInvariant] (Γ : Subgroup G) [Countable Γ] {F : Set G}
    (hF : IsFundamentalDomain Γ F μ) {α ψ : G → ℂ} (hα : Continuous α) (hψ : Continuous ψ)
    (hinv : ∀ γ ∈ Γ, ∀ g, ψ (γ * g) = ψ g) (hn : (∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ) = 1) (x : G) (k : ℕ)
    (hk : {γ : G | γ ∈ Γ ∧ ∃ a ∈ tsupport α, ∃ b ∈ tsupport α, γ = x * a * b⁻¹ * x⁻¹}.encard ≤ k) :
    (∫⁻ y, ‖α y‖ₑ * ‖ψ (x * y)‖ₑ ∂μ) ^ 2 ≤ k * ∫⁻ y, ‖α y‖ₑ ^ 2 ∂μ := by
  set a : G → ℝ≥0∞ := fun w => ‖α (x⁻¹ * w)‖ₑ with ha
  have ham : Measurable a := (hα.comp (continuous_const.mul continuous_id)).enorm.measurable
  have hψm : Measurable fun w => ‖ψ w‖ₑ := hψ.enorm.measurable
  have htr : ∀ γ : Γ, Measurable fun w => a ((γ : G) * w) :=
    fun γ => ham.comp (measurable_const_mul _)
  have e1 : ∫⁻ y, ‖α y‖ₑ * ‖ψ (x * y)‖ₑ ∂μ = ∫⁻ w in F, (∑' γ : Γ, a ((γ : G) * w)) * ‖ψ w‖ₑ ∂μ := by
    have h1 := lintegral_mul_left_eq_self (μ := μ) (fun w => a w * ‖ψ w‖ₑ) x
    simp only [ha, inv_mul_cancel_left] at h1
    rw [h1, hF.lintegral_eq_tsum'', ← lintegral_tsum]
    · refine lintegral_congr fun w => ?_
      rw [← ENNReal.tsum_mul_right]
      refine tsum_congr fun γ => ?_
      rw [Subgroup.smul_def, smul_eq_mul, hinv _ γ.2]
    · intro γ
      simp only [Subgroup.smul_def, smul_eq_mul, hinv _ γ.2]
      exact ((htr γ).mul hψm).aemeasurable
  have e2 : ∫⁻ y, ‖α y‖ₑ ^ 2 ∂μ = ∫⁻ w in F, ∑' γ : Γ, a ((γ : G) * w) ^ 2 ∂μ := by
    have h1 := lintegral_mul_left_eq_self (μ := μ) (fun w => a w ^ 2) x
    simp only [ha, inv_mul_cancel_left] at h1
    rw [h1, hF.lintegral_eq_tsum'', ← lintegral_tsum]
    · rfl
    · intro γ
      exact ((htr γ).pow_const 2).aemeasurable
  have hK : Measurable fun w => ∑' γ : Γ, a ((γ : G) * w) := Measurable.ennreal_tsum htr
  rw [e1, e2, ← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top k)]
  refine (sq_lintegral_mul_le _ hK.aemeasurable hψm.aemeasurable).trans ?_
  rw [hn, mul_one]
  refine lintegral_mono fun w => ?_
  have := sq_tsum_le (fun γ : Γ => ‖α (x⁻¹ * ((γ : G) * w))‖₊) k (encard_support_le Γ α x w k hk)
  simpa [ha, enorm_eq_nnnorm] using this

theorem pointwise (μ : Measure G) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] (Γ : Subgroup G) [Countable Γ]
    {α : G → ℂ} {δ : ℝ} {F : Set G} (hα : Continuous α) (hc : HasCompactSupport α) (hδ : 0 < δ)
    (hF : IsFundamentalDomain Γ F μ) : ∃ C₀ : ℝ, ∀ ψ : G → ℂ, Continuous ψ → (∀ γ ∈ Γ, ∀ g, ψ (γ * g) = ψ g) →
      (∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ (x * y) ∂μ = s * ψ x) → (∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ) = 1 →
      ∀ (x : G) (k : ℕ), {γ : G | γ ∈ Γ ∧ ∃ a ∈ tsupport α, ∃ b ∈ tsupport α, γ = x * a * b⁻¹ * x⁻¹}.encard ≤ k →
        ‖ψ x‖ ^ 2 ≤ C₀ * k := by
  refine ⟨(δ ^ 2)⁻¹ * (∫⁻ y, ‖α y‖ₑ ^ 2 ∂μ).toReal, ?_⟩
  rintro ψ hψ hinv ⟨s, hs, hrep⟩ hn x k hk
  have hA : (∫⁻ y, ‖α y‖ₑ ^ 2 ∂μ) ≠ ⊤ := by
    have hc2 : HasCompactSupport ((fun z : ℂ => ‖z‖ ^ 2) ∘ α) :=
      HasCompactSupport.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) hc (by simp)
    have hi : Integrable ((fun z : ℂ => ‖z‖ ^ 2) ∘ α) μ :=
      Continuous.integrable_of_hasCompactSupport ((continuous_norm.pow 2).comp hα) hc2
    have := hi.2.ne
    simpa [HasFiniteIntegral, enorm_pow] using this
  have h1 : ‖s‖ₑ * ‖ψ x‖ₑ ≤ ∫⁻ y, ‖α y‖ₑ * ‖ψ (x * y)‖ₑ ∂μ := by
    rw [← enorm_mul, ← hrep x]
    exact (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (by simp only [enorm_mul]))
  have h3 : (‖s‖ₑ * ‖ψ x‖ₑ) ^ 2 ≤ k * ∫⁻ y, ‖α y‖ₑ ^ 2 ∂μ :=
    (pow_le_pow_left' h1 2).trans (sq_lintegral_le μ _ hF hα hψ hinv hn x k hk)
  have h4 : (‖s‖ * ‖ψ x‖) ^ 2 ≤ k * (∫⁻ y, ‖α y‖ₑ ^ 2 ∂μ).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top k) hA) h3
    simpa [ENNReal.toReal_mul, ENNReal.toReal_pow, toReal_enorm] using this
  have hδ2 : 0 < δ ^ 2 := by positivity
  have h5 : δ ^ 2 * ‖ψ x‖ ^ 2 ≤ (‖s‖ * ‖ψ x‖) ^ 2 := by
    rw [mul_pow]
    gcongr
  have h6 := h5.trans h4
  rw [mul_assoc, inv_mul_eq_div, le_div_iff₀ hδ2]
  nlinarith [h6]

end GlobalTheory.CompanionTheory.Conc.BesselPt

open GlobalTheory.CompanionTheory.Conc.BesselPt in

theorem GlobalTheory.CompanionTheory.Conc.besselPt : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] (α : GA E N → ℂ) (δ : ℝ) (F : Set (GA E N)), Continuous α → HasCompactSupport α → 0 < δ →
  IsFundamentalDomain (latticeGL E N) F μ → ∃ C₀ : ℝ, ∀ ψ : GA E N → ℂ, Continuous ψ → (∀ γ ∈ latticeGL E N, ∀ g, ψ (γ * g) = ψ g) →
  (∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ (x * y) ∂μ = s * ψ x) → (∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ) = 1 →
  ∀ (x : GA E N) (k : ℕ), {γ : GA E N | γ ∈ latticeGL E N ∧ ∃ a ∈ tsupport α, ∃ b ∈ tsupport α, γ = x * a * b⁻¹ * x⁻¹}.encard ≤ k →
    ‖ψ x‖ ^ 2 ≤ C₀ * k := by
  intro E _ _ _ N _ _ μ _ α δ F hα hc hδ hF
  haveI : Countable (latticeGL E N) := GlobalTheory.DiscreteUnit.countable_latticeGL
  exact pointwise μ (latticeGL E N) hα hc hδ hF
