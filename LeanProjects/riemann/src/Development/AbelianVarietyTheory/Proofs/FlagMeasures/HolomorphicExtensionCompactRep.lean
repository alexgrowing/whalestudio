import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IntegralAgainstLinearApply

open Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec
open scoped InnerProductSpace
open MeasureTheory Filter Topology
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.HolExt

theorem differentiable_det (n : ℕ) :
    Differentiable ℂ fun y : Fin n → Fin n → ℂ => (Matrix.of y).det := by
  simp only [Matrix.det_apply', Matrix.of_apply]
  fun_prop

theorem differentiable_adjugate (n : ℕ) (i j : Fin n) :
    Differentiable ℂ fun y : Fin n → Fin n → ℂ => (Matrix.of y).adjugate i j := by
  simp only [Matrix.adjugate_apply]
  have : (fun y : Fin n → Fin n → ℂ => ((Matrix.of y).updateRow j (Pi.single i 1)).det) =
      (fun y : Fin n → Fin n → ℂ => (Matrix.of y).det) ∘ fun y => Function.update y j (Pi.single i 1) := rfl
  rw [this]
  refine (differentiable_det n).comp (differentiable_pi.2 fun a => ?_)
  by_cases h : a = j
  · subst h
    simp
  · simp only [Function.update_of_ne h]
    fun_prop

theorem differentiableOn_inv (n : ℕ) (i j : Fin n) :
    DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => (Matrix.of y)⁻¹ i j) {y | IsUnit (Matrix.of y)} := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  refine ((differentiable_det n).differentiableOn.inv fun y hy => ?_).mul
    (differentiable_adjugate n i j).differentiableOn
  exact ((Matrix.isUnit_iff_isUnit_det _).1 hy).ne_zero

def peak {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := 1 + 2 * n + 2 * g.trace.re

theorem peak_coe {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    ((peak g : ℝ) : ℂ) = 1 + 2 * n + g.trace + gᴴ.trace := by
  rw [Matrix.trace_conjTranspose, add_assoc, Complex.star_def, Complex.add_conj, peak]
  push_cast
  ring

theorem peak_pos {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ} (hg : gᴴ * g = 1) : 0 < peak g := by
  have h := (Matrix.posSemidef_conjTranspose_mul_self (g + 1)).trace_nonneg
  have h2 := (Complex.le_def.1 h).1
  simp only [conjTranspose_add, conjTranspose_one, Matrix.add_mul, Matrix.mul_add, hg, Matrix.mul_one,
    Matrix.one_mul, trace_add, trace_one, trace_conjTranspose, Fintype.card_fin, Complex.add_re,
    Complex.natCast_re, Complex.star_def, Complex.conj_re, Complex.zero_re] at h2
  unfold peak
  linarith

theorem peak_lt {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ} (hg : gᴴ * g = 1) (h1 : g ≠ 1) :
    peak g < peak (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have h := (Matrix.posSemidef_conjTranspose_mul_self (g - 1)).trace_nonneg
  have hne : ((g - 1)ᴴ * (g - 1)).trace ≠ 0 := by
    rw [Ne, Matrix.trace_conjTranspose_mul_self_eq_zero_iff, sub_eq_zero]
    exact h1
  have h2 := (Complex.lt_def.1 (lt_of_le_of_ne h hne.symm)).1
  simp only [conjTranspose_sub, conjTranspose_one, Matrix.sub_mul, Matrix.mul_sub, hg, Matrix.mul_one,
    Matrix.one_mul, trace_sub, trace_one, trace_conjTranspose, Fintype.card_fin, Complex.sub_re,
    Complex.natCast_re, Complex.star_def, Complex.conj_re, Complex.zero_re] at h2
  simp only [peak, trace_one, Fintype.card_fin, Complex.natCast_re]
  linarith

def intCLM {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    [SecondCountableTopology K]
    (μ : Measure K) [IsFiniteMeasure μ] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    (p : K → B) (hp : Continuous p) : C(K, ℂ) →L[ℂ] B := GlobalTheory.IntegralAgainstMeasure.integralAgainst μ ⟨p, hp⟩

theorem exists_holomorphic_extension : ∀ (n : ℕ) (ε : Fin n → Bool) (B : Type) [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B] (π : Matrix (Fin n) (Fin n) ℂ → B), π 1 = 1 → (∀ a ∈ Formalism.REAL.Kset ε, ∀ b ∈ Formalism.REAL.Kset ε, π (a * b) = π a * π b) → ContinuousOn π (Formalism.REAL.Kset ε) → ∃ τ : Matrix (Fin n) (Fin n) ℂ → B, DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => τ (Matrix.of y)) {y | IsUnit (Matrix.of y)} ∧ ∀ k ∈ Formalism.REAL.Kset ε, τ k = π k := by
  intro n ε B _ _ _ π h1 hmul hcont
  have hemb : Topology.IsEmbedding (fun k : KG ε => toMK k) :=
    (isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  haveI : TopologicalSpace.MetrizableSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (TopologicalSpace.MetrizableSpace (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : TopologicalSpace.MetrizableSpace (KG ε) := hemb.metrizableSpace
  haveI : SecondCountableTopology (KG ε) := hemb.secondCountableTopology
  set μ := muK ε
  have hmem : ∀ g : KG ε, toMK g ∈ Kset ε := fun g => g.2
  have hun : ∀ x ∈ Kset ε, xᴴ * x = 1 := fun x hx => Unitary.star_mul_self_of_mem hx.1
  have hu : Continuous fun g : KG ε => toMK g := hemb.continuous
  have hb : Continuous fun g : KG ε => π (toMK g) := hcont.comp_continuous hu hmem
  have hc : Continuous fun g : KG ε => peak (toMK g) := by
    unfold peak
    fun_prop
  have hone : toMK (1 : KG ε) = 1 := rfl
  have hlim := tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn
    (μ := μ) (s := Set.univ) (x₀ := (1 : KG ε)) (c := fun g : KG ε => peak (toMK g))
    (g := fun g : KG ε => π (toMK g)) isCompact_univ hc.continuousOn
    (fun y _ hy => peak_lt (hun _ (hmem y)) fun h => hy (hemb.injective h))
    (fun y _ => (peak_pos (hun _ (hmem y))).le) (peak_pos (hun _ (hmem 1))) (by simp) hb.continuousOn
  simp only [Measure.restrict_univ, hone, h1] at hlim
  obtain ⟨N, hN⟩ := (hlim.eventually (Metric.ball_mem_nhds _ one_pos)).exists
  set c := ∫ g : KG ε, peak (toMK g) ^ N ∂μ
  set A := ∫ g : KG ε, peak (toMK g) ^ N • π (toMK g) ∂μ with hA
  have hint : Integrable (fun g : KG ε => peak (toMK g) ^ N • π (toMK g)) μ :=
    ((hc.pow N).smul hb).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hAu : ∃ A' : B, A * A' = 1 := by
    have e3 : ‖(1 : B) - c⁻¹ • A‖ < 1 := by
      rw [← dist_eq_norm, dist_comm]
      exact hN
    obtain ⟨u, hu⟩ := isUnit_one_sub_of_norm_lt_one e3
    rw [sub_sub_cancel] at hu
    refine ⟨c⁻¹ • (↑u⁻¹ : B), ?_⟩
    rw [mul_smul_comm, ← smul_mul_assoc, ← hu, Units.mul_inv]
  obtain ⟨A', hA'⟩ := hAu
  have hform : ∀ x ∈ Kset ε, π x * A = ∫ g : KG ε, peak (xᴴ * toMK g) ^ N • π (toMK g) ∂μ := by
    intro x hx
    obtain ⟨z, hz⟩ : x ∈ Set.range (fun g : KG ε => toMK g) := by
      rw [range_toMK]; exact hx
    have hz' : toMK z = x := hz
    have := (ContinuousLinearMap.mul ℂ B (π x)).integral_comp_comm hint
    rw [ContinuousLinearMap.mul_apply'] at this
    rw [hA, ← this,
      ← integral_mul_left_eq_self (fun g : KG ε => peak (xᴴ * toMK g) ^ N • π (toMK g)) z]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    have e : toMK (z * g) = x * toMK g := by rw [← hz']; rfl
    simp only [e]
    rw [← Matrix.mul_assoc, hun x hx, Matrix.one_mul, hmul _ hx _ (hmem g), ContinuousLinearMap.mul_apply',
      mul_smul_comm]
  let e : Fin n → Fin n → C(KG ε, ℂ) := fun i j => ⟨fun g => toMK g i j, hu.matrix_elem i j⟩
  let F : Matrix (Fin n) (Fin n) ℂ → C(KG ε, ℂ) := fun y =>
    ((1 + 2 * n : ℂ) • (1 : C(KG ε, ℂ)) + ∑ i, ∑ j, y⁻¹ i j • e j i + ∑ i, ∑ j, y j i • star (e j i)) ^ N
  refine ⟨fun y => intCLM μ _ hb (F y) * A', ?_, fun k hk => ?_⟩
  · refine DifferentiableOn.mul_const ((intCLM μ _ hb).differentiable.comp_differentiableOn ?_) _
    refine DifferentiableOn.pow (DifferentiableOn.add (DifferentiableOn.add (differentiableOn_const _) ?_) ?_) N
    · exact DifferentiableOn.fun_sum fun i _ => DifferentiableOn.fun_sum fun j _ =>
        (differentiableOn_inv n i j).smul_const _
    · refine DifferentiableOn.fun_sum fun i _ => DifferentiableOn.fun_sum fun j _ =>
        DifferentiableOn.smul_const ?_ _
      simp only [Matrix.of_apply]
      fun_prop
  · have hinv : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv (hun k hk)
    have hI : intCLM μ _ hb (F k) = π k * A := by
      rw [hform k hk]
      show ∫ g, F k g • π (toMK g) ∂μ = _
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      have : F k g = ((peak (kᴴ * toMK g) ^ N : ℝ) : ℂ) := by
        rw [Complex.ofReal_pow, peak_coe, conjTranspose_mul, conjTranspose_conjTranspose]
        simp [F, e, hinv, Matrix.trace, Matrix.mul_apply, mul_comm]
      simp only [this, Complex.coe_smul]
    show intCLM μ _ hb (F k) * A' = π k
    rw [hI, mul_assoc, hA', mul_one]

end GlobalTheory.HolExt
