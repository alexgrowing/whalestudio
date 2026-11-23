import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Admissible
import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving

open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

namespace GlobalTheory.ThA.TorusJac

variable {k r : ℕ}

noncomputable def dT (k r : ℕ) (α : ℂ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r then α ^ (r - i.val) else if i.val ≤ r + k then 1 else ((star α) ^ (i.val - (r + k)))⁻¹

theorem aT_eq (α : ℂ) : aT k r α = Matrix.diagonal (dT k r α) := rfl

theorem dT_mul (α β : ℂ) (i : Fin (2 * r + k + 1)) : dT k r α i * dT k r β i = dT k r (α * β) i := by
  unfold dT
  split_ifs
  · rw [mul_pow]
  · simp
  · rw [star_mul', mul_pow, mul_inv]

theorem dT_one (i : Fin (2 * r + k + 1)) : dT k r 1 i = 1 := by
  unfold dT
  split_ifs <;> simp

theorem aT_mul (α β : ℂ) : aT k r α * aT k r β = aT k r (α * β) := by
  rw [aT_eq, aT_eq, aT_eq, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact dT_mul α β i

theorem aT_one : aT k r 1 = 1 := by
  rw [aT_eq, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact dT_one i

theorem aT_inv {α : ℂ} (h : α ≠ 0) : (aT k r α)⁻¹ = aT k r α⁻¹ :=
  Matrix.inv_eq_right_inv (by rw [aT_mul, mul_inv_cancel₀ h, aT_one])

theorem aT_unit {α : ℂ} (h : α ≠ 0) : IsUnit (aT k r α).det :=
  Matrix.isUnit_det_of_right_inverse (B := aT k r α⁻¹) (by rw [aT_mul, mul_inv_cancel₀ h, aT_one])

theorem aT_real (t : ℝ) : aT k r (t : ℂ) = B.aDil k r t := by
  unfold aT B.aDil
  congr 1
  funext i
  split_ifs <;> simp

theorem aT_mem {α : ℂ} (h : α ≠ 0) : aT k r α ∈ UH (Hpk k r) := by
  show (aT k r α)ᴴ * Hpk k r * aT k r α = Hpk k r
  rw [aT_eq, Matrix.diagonal_conjTranspose]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hs : star α ≠ 0 := star_ne_zero.2 h
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, Pi.star_apply]
  by_cases h1 : i.val < r ∧ i.val + j.val = 2 * r + k
  · rw [if_pos h1]
    unfold dT
    rw [if_pos h1.1, if_neg (by omega), if_neg (by omega), show j.val - (r + k) = r - i.val by omega, star_pow,
      mul_one, mul_inv_cancel₀ (pow_ne_zero _ hs)]
  rw [if_neg h1]
  by_cases h2 : j.val < r ∧ i.val + j.val = 2 * r + k
  · rw [if_pos h2]
    unfold dT
    rw [if_pos h2.1, if_neg (by omega), if_neg (by omega), show i.val - (r + k) = r - j.val by omega, star_inv₀,
      star_pow, star_star, mul_one, inv_mul_cancel₀ (pow_ne_zero _ h)]
  rw [if_neg h2]
  by_cases h3 : r ≤ i.val ∧ i.val ≤ r + k ∧ i = j
  · rw [if_pos h3]
    obtain ⟨h3, h4, rfl⟩ := h3
    unfold dT
    rw [if_neg (show ¬ i.val < r by omega), if_pos h4, star_one, one_mul, mul_one]
  rw [if_neg h3, mul_zero, zero_mul]

theorem conj_entry {α : ℂ} (h : α ≠ 0) (g : B.Mat k r) (i j : Fin (2 * r + k + 1))
    (hg : g i j = if i = j then 1 else 0) :
    (aT k r α * g * (aT k r α)⁻¹) i j = if i = j then 1 else 0 := by
  rw [aT_inv h, aT_eq, aT_eq, Matrix.mul_diagonal, Matrix.diagonal_mul, hg]
  split_ifs with e
  · subst e
    rw [mul_one, dT_mul, mul_inv_cancel₀ h, dT_one]
  · simp

theorem conj_mem {α : ℂ} (h : α ≠ 0) {n : B.Mat k r} (hn : n ∈ Nset k r) :
    aT k r α * n * (aT k r α)⁻¹ ∈ Nset k r := by
  have hG := Formalism.FourierDecayAlt.Final.closed_subgroup_general_linear k r
  obtain ⟨h1, h2, h3⟩ := hn
  refine ⟨hG.mul_mem _ (hG.mul_mem _ (aT_mem h) _ h1) _ (hG.inv_mem _ (aT_mem h)), fun a i hi => ?_,
    fun i j a b c => ?_⟩
  · exact conj_entry h n _ _ (h2 a i hi)
  · exact conj_entry h n _ _ (h3 i j a b c)

theorem contOn : ContinuousOn (aT k r) (Metric.sphere (0 : ℂ) 1) := by
  have : ContinuousOn (dT k r) (Metric.sphere (0 : ℂ) 1) := by
    refine continuousOn_pi.2 fun i => ?_
    unfold dT
    split_ifs
    · fun_prop
    · fun_prop
    · refine ContinuousOn.inv₀ (by fun_prop) fun x hx => pow_ne_zero _ (star_ne_zero.2 ?_)
      exact ne_zero_of_mem_unit_sphere ⟨x, hx⟩
  exact (Continuous.matrix_diagonal continuous_id).comp_continuousOn this

theorem circle_compact : IsCompact (aT k r '' Metric.sphere (0 : ℂ) 1) :=
  (isCompact_sphere _ _).image_of_continuousOn contOn

theorem circle_subgroup : B2.IsClosedSubgroup (aT k r '' Metric.sphere (0 : ℂ) 1) where
  one_mem := ⟨1, by simp, aT_one⟩
  mul_mem := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    refine ⟨a * b, ?_, (aT_mul a b).symm⟩
    simp only [mem_sphere_zero_iff_norm] at *
    rw [norm_mul, ha, hb, mul_one]
  inv_mem := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨a⁻¹, ?_, (aT_inv (ne_zero_of_mem_unit_sphere ⟨a, ha⟩)).symm⟩
    simp only [mem_sphere_zero_iff_norm] at *
    rw [norm_inv, ha, inv_one]
  unit := by
    rintro _ ⟨a, ha, rfl⟩
    exact aT_unit (ne_zero_of_mem_unit_sphere ⟨a, ha⟩)
  closed := circle_compact.isClosed

theorem conj_cont (a : B.Mat k r) : Continuous (conjM a : Mt k r → Mt k r) :=
  (continuous_const.matrix_mul (continuous_id (X := B.Mat k r))).matrix_mul continuous_const

theorem conj_conj (a b : B.Mat k r) : (conjM a : Mt k r → Mt k r) ∘ conjM b = conjM (a * b) := by
  funext x
  show (a * (b * Matrix.of x * b⁻¹) * a⁻¹ : B.Mat k r) = a * b * Matrix.of x * (a * b)⁻¹
  simp only [Matrix.mul_inv_rev, Matrix.mul_assoc]

theorem haar_map_conj (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Nset k r) μ) (α : ℂ) (h : α ≠ 0) :
    μ.map (conjM (aT k r α)) = ENNReal.ofReal ((‖α‖ ^ B.kap k r)⁻¹) • μ := by
  have hp : 0 < ‖α‖ := norm_pos_iff.2 h
  have hc : (‖α‖ : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hu : α / (‖α‖ : ℂ) ∈ Metric.sphere (0 : ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real, norm_norm, div_self hp.ne']
  have e : aT k r α = B.aDil k r ‖α‖ * aT k r (α / (‖α‖ : ℂ)) := by
    rw [← aT_real, aT_mul, mul_div_cancel₀ _ hc]
  have h1 : μ.map (conjM (aT k r (α / (‖α‖ : ℂ)))) = μ := by
    refine Formalism.FourierDecayAlt.Final.compact_conjugation k r _ _ μ (Formalism.FourierDecayAlt.Final.closed_subgroup_unipotent_radical k r) circle_subgroup circle_compact
      ?_ hμ _ ⟨_, hu, rfl⟩
    rintro _ ⟨a, ha, rfl⟩ u hu
    exact conj_mem (ne_zero_of_mem_unit_sphere ⟨a, ha⟩) hu
  rw [e, ← conj_conj, ← Measure.map_map (conj_cont _).measurable (conj_cont _).measurable, h1]
  exact Formalism.FourierDecayAlt.Final.dilation_jacobian_formula k r μ hμ _ hp

theorem muN_map_conj : ∀ (k r : ℕ) (α : ℂ), α ≠ 0 →
    (D.muN k r).map (conjM (aT k r α)) = ENNReal.ofReal ((‖α‖ ^ B.kap k r)⁻¹) • D.muN k r :=
  fun k r α h => haar_map_conj _ (Formalism.FourierDecayAlt.Final.d_muNHaar k r) α h

end GlobalTheory.ThA.TorusJac
