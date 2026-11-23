import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DHRealAdSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousSlice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergDerivativePreservesSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SobolevPointwiseBoundWordsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurablePeriodicArchRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzPolynomialDecayWordsStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix
open scoped Classical

noncomputable section
namespace GlobalTheory.SobClass

theorem wordH_mem_sch {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) :
    ∀ l : List ((κ → AF F) × (κ → AF F)), (∀ w ∈ l, IsArch w) → ∀ Φ ∈ schA F κ, wordH ψ l Φ ∈ schA F κ := by
  intro l
  induction l with
  | nil => intro _ Φ hΦ; exact hΦ
  | cons w l ih =>
    intro hl Φ hΦ
    rw [wordH_cons]
    exact GlobalTheory.T.heisenberg_derivative_preserves_schwartz F κ ψ hψ w (hl w (by simp)) _ (ih (fun v hv => hl v (by simp [hv])) Φ hΦ)

theorem sqrt_bound (Q M B t : ℝ) (hQ : 0 ≤ Q) (hM : 1 ≤ M) (hB : 0 ≤ B) (ht : 0 ≤ t) (h : t ^ 2 ≤ Q * (M * B)) :
    t ≤ √Q * (M * (1 + B)) := by
  have h1 : M * B ≤ (M * (1 + B)) ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.2 hM) hB]
  have h2 : t ≤ √(Q * (M * B)) := Real.le_sqrt_of_sq_le h
  calc t ≤ √(Q * (M * B)) := h2
    _ = √Q * √(M * B) := Real.sqrt_mul hQ _
    _ ≤ √Q * (M * (1 + B)) := by
        gcongr
        calc √(M * B) ≤ √((M * (1 + B)) ^ 2) := Real.sqrt_le_sqrt h1
          _ = M * (1 + B) := Real.sqrt_sq (by nlinarith)

theorem sob_class : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (N : ℕ) (ψ : AddChar (AF F) ℂ), IsStd ψ → ∃ (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧ ∃ (ℓ a : ℕ) (C : ℝ), ∀ Ψ ∈ schA F κ, ∀ m : ℕ, 1 ≤ m → (∀ x a' : κ → AF F, (∀ i, evI F (a' i) = 0 ∧ ∀ v, evFin F v (a' i) ∈ v.adicCompletionIntegers F) → Ψ (x + (m : AF F) • a') = Ψ x) → ∀ B : ℝ, 0 ≤ B → (∀ l : List ((κ → AF F) × (κ → AF F)), l.length ≤ ℓ → (∀ w ∈ l, IsArchUnit w) → ∫⁻ x, ‖wordH ψ l Ψ x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal B) → ∀ x : κ → AF F, ‖Ψ x‖ * (1 + ∑ i, ‖evI F (x i)‖) ^ N ≤ C * (m : ℝ) ^ a * (1 + B) := by
  intro F _ _ κ _ N ψ hψ
  obtain ⟨μ, hμ, a, Cb, hB⟩ := GlobalTheory.T.measurable_periodic_arch_restriction F κ
  obtain ⟨Lw, K, hLw, hW⟩ := GlobalTheory.T.schwartz_polynomial_decay_words F κ ψ hψ N
  obtain ⟨L, D, Cs, hL, hS⟩ := GlobalTheory.T.sobolev_pointwise_bound_words F κ ψ hψ
  refine ⟨μ, hμ, D + N, a, max K 0 * Lw.card * √(max Cs 0 * L.card * max Cb 0),
    fun Ψ hΨ m hm hper B hB0 hwords x => ?_⟩
  have hm1 : (1 : ℝ) ≤ (m : ℝ) ^ a := one_le_pow₀ (by exact_mod_cast hm)
  have hQ : 0 ≤ max Cs 0 * L.card * max Cb 0 := by positivity
  have hterm : ∀ l ∈ Lw, ‖wordH ψ l Ψ x‖ ≤ √(max Cs 0 * L.card * max Cb 0) * ((m : ℝ) ^ a * (1 + B)) := by
    intro l hl
    have hmem : wordH ψ l Ψ ∈ schA F κ := wordH_mem_sch ψ hψ l (fun w hw => ((hLw l hl).2 w hw).1) Ψ hΨ
    have h2 : ∀ l' ∈ L, ∫⁻ y : κ → mixedEmbedding.mixedSpace F, ‖wordH ψ l' (wordH ψ l Ψ) (x + archInc F y)‖ₑ ^ 2 ≤
        ENNReal.ofReal (max Cb 0 * (m : ℝ) ^ a * B) := by
      intro l' hl'
      rw [← wordH_append]
      have hu : ∀ w ∈ l' ++ l, IsArchUnit w := by
        intro w hw
        rcases List.mem_append.1 hw with hw | hw
        · exact (hL l' hl').2 w hw
        · exact (hLw l hl).2 w hw
      have hmem' : wordH ψ (l' ++ l) Ψ ∈ schA F κ := wordH_mem_sch ψ hψ _ (fun w hw => (hu w hw).1) Ψ hΨ
      have hper' : PerM F m (wordH ψ (l' ++ l) Ψ) := wordH_perM ψ hper _ (fun w hw => (hu w hw).1)
      have hmeas : Measurable fun y : κ → mixedEmbedding.mixedSpace F => ‖wordH ψ (l' ++ l) Ψ (x + archInc F y)‖ₑ ^ 2 :=
        (continuous_slice hmem' x).measurable.enorm.pow_const 2
      have h5 := hB m hm (fun z => ‖wordH ψ (l' ++ l) Ψ z‖ₑ ^ 2) (fun z a' ha => by rw [hper' z a' ha]) x hmeas
      have hw := hwords (l' ++ l) (by rw [List.length_append]; have := (hL l' hl').1; have := (hLw l hl).1; omega) hu
      refine h5.trans ?_
      calc ENNReal.ofReal (Cb * (m : ℝ) ^ a) * ∫⁻ z, ‖wordH ψ (l' ++ l) Ψ z‖ₑ ^ 2 ∂μ
          ≤ ENNReal.ofReal (max Cb 0 * (m : ℝ) ^ a) * ENNReal.ofReal B := by
            gcongr
            exact le_max_left _ _
        _ = ENNReal.ofReal (max Cb 0 * (m : ℝ) ^ a * B) := (ENNReal.ofReal_mul (by positivity)).symm
    have h3 : ‖wordH ψ l Ψ x‖ₑ ^ 2 ≤ ENNReal.ofReal (max Cs 0 * L.card * max Cb 0 * ((m : ℝ) ^ a * B)) := by
      refine (hS _ hmem x).trans ?_
      calc ENNReal.ofReal Cs * ∑ l' ∈ L, ∫⁻ y : κ → mixedEmbedding.mixedSpace F, ‖wordH ψ l' (wordH ψ l Ψ) (x + archInc F y)‖ₑ ^ 2
          ≤ ENNReal.ofReal (max Cs 0) * ∑ _l' ∈ L, ENNReal.ofReal (max Cb 0 * (m : ℝ) ^ a * B) := by
            gcongr with l' hl'
            · exact le_max_left _ _
            · exact h2 l' hl'
        _ = ENNReal.ofReal (max Cs 0 * L.card * max Cb 0 * ((m : ℝ) ^ a * B)) := by
            rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            ring
    have h4 : ‖wordH ψ l Ψ x‖ ^ 2 ≤ max Cs 0 * L.card * max Cb 0 * ((m : ℝ) ^ a * B) := by
      rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)] at h3
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3
    exact sqrt_bound _ _ _ _ hQ hm1 hB0 (norm_nonneg _) (by simpa [mul_assoc] using h4)
  calc ‖Ψ x‖ * (1 + ∑ i, ‖evI F (x i)‖) ^ N ≤ K * ∑ l ∈ Lw, ‖wordH ψ l Ψ x‖ := hW Ψ x
    _ ≤ max K 0 * ∑ l ∈ Lw, ‖wordH ψ l Ψ x‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    _ ≤ max K 0 * ∑ _l ∈ Lw, √(max Cs 0 * L.card * max Cb 0) * ((m : ℝ) ^ a * (1 + B)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (le_max_right _ _)
    _ = max K 0 * Lw.card * √(max Cs 0 * L.card * max Cb 0) * (m : ℝ) ^ a * (1 + B) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

end GlobalTheory.SobClass
end
