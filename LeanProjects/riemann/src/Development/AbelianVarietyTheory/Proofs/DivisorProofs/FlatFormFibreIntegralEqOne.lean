import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapFlatDerivativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgePowerEqFactorialDetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumePeriodTorusEqDetImaginaryStatement

open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory.FibreInt

theorem flatOf_single_one {g : ℕ} (τ0 : Matrix (Fin g) (Fin g) ℂ) (i : Fin g) :
    flatOf τ0 (Pi.single i 1) = Sum.elim (0 : Fin g → ℝ) (Pi.single i (1 : ℝ)) := by
  have h1 : (fun k => ((Pi.single i (1 : ℂ) : Fin g → ℂ) k).im) = 0 := by
    ext k; by_cases h : k = i <;> simp [h]
  have h2 : (fun k => ((Pi.single i (1 : ℂ) : Fin g → ℂ) k).re) = Pi.single i (1 : ℝ) := by
    ext k; by_cases h : k = i <;> simp [h]
  simp only [flatOf, h1, h2, Matrix.zero_vecMul, sub_zero]

theorem flatOf_single_I {g : ℕ} (τ0 : Matrix (Fin g) (Fin g) ℂ) (i : Fin g) :
    flatOf τ0 (Pi.single i Complex.I) = Sum.elim ((τ0.map Complex.im)⁻¹ i)
      (-((τ0.map Complex.im)⁻¹ i ᵥ* τ0.map Complex.re)) := by
  have h1 : (fun k => ((Pi.single i Complex.I : Fin g → ℂ) k).im) = Pi.single i (1 : ℝ) := by
    ext k; by_cases h : k = i <;> simp [h]
  have h2 : (fun k => ((Pi.single i Complex.I : Fin g → ℂ) k).re) = 0 := by
    ext k; by_cases h : k = i <;> simp [h]
  simp only [flatOf, h1, h2, Matrix.single_one_vecMul, zero_sub]
  rfl

theorem riem_flatOf_single {g : ℕ} (τ0 : Matrix (Fin g) (Fin g) ℂ) (hs : τ0.IsSymm) (i j : Fin g) :
    riem (flatOf τ0 (Pi.single i 1)) (flatOf τ0 (Pi.single j 1)) = 0 ∧
    riem (flatOf τ0 (Pi.single i Complex.I)) (flatOf τ0 (Pi.single j Complex.I)) = 0 ∧
    riem (flatOf τ0 (Pi.single i 1)) (flatOf τ0 (Pi.single j Complex.I)) =
      (τ0.map Complex.im)⁻¹ j i := by
  rw [flatOf_single_one, flatOf_single_one, flatOf_single_I, flatOf_single_I]
  refine ⟨by simp [riem], ?_, ?_⟩
  · have hX : (τ0.map Complex.re).IsSymm := by
      rw [Matrix.IsSymm, ← Matrix.transpose_map, hs.eq]
    set X := τ0.map Complex.re
    set a := (τ0.map Complex.im)⁻¹ i
    set c := (τ0.map Complex.im)⁻¹ j
    have e : riem (Sum.elim a (-(a ᵥ* X))) (Sum.elim c (-(c ᵥ* X))) =
        -((a ᵥ* X) ⬝ᵥ c) + (c ᵥ* X) ⬝ᵥ a := by
      simp only [riem, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, dotProduct,
        ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    have e2 : (c ᵥ* X) ⬝ᵥ a = (a ᵥ* X) ⬝ᵥ c := by
      rw [← Matrix.dotProduct_mulVec c, dotProduct_comm, ← Matrix.vecMul_transpose, hX.eq]
    rw [e, e2]
    ring
  · simp [riem, Pi.single_apply]

theorem flatForm_apply {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (τ : E → Matrix (Fin g) (Fin g) ℂ) (P u w : Pt E g) :
    om0 τ P ![u, w] = riem (dflat τ P u) (dflat τ P w) := rfl

theorem fibreIntegral_flatForm : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ},
    IsPeriodMap B τ → ∀ b ∈ B, fibreInt τ (om0 τ) b = 1 := by
  intro g E _ _ _ B τ hτ b hb
  obtain ⟨hsym, hpos⟩ := hτ.2.2 b hb
  have hc : ∀ z : Fin g → ℂ, wedgePow (om0 τ (b, z)) g (fun k => ((0 : E),
      Pi.single k.1 (if k.2 = 0 then (1 : ℂ) else Complex.I))) / (g.factorial : ℝ)
        = ((τ b).map Complex.im)⁻¹.det := by
    intro z
    rw [GlobalTheory.T.wedge_power_eq_factorial_det (om0 τ (b, z)) g _ ((τ b).map Complex.im)⁻¹ᵀ]
    · rw [det_transpose]
      field_simp
    all_goals intro i j; simp only [flatForm_apply, GlobalTheory.T.period_map_flat_derivative hτ b hb]
    · simpa using (riem_flatOf_single (τ b) hsym i j).1
    · simpa using (riem_flatOf_single (τ b) hsym i j).2.1
    · simpa using (riem_flatOf_single (τ b) hsym i j).2.2
  unfold fibreInt
  simp only [hc]
  rw [setIntegral_const, measureReal_def, GlobalTheory.T.volume_period_torus_eq_det_imaginary, ENNReal.toReal_ofReal (abs_nonneg _),
    abs_of_pos hpos.det_pos, smul_eq_mul, det_nonsing_inv, Ring.inverse_eq_inv',
    mul_inv_cancel₀ hpos.det_pos.ne']

end GlobalTheory.FibreInt
