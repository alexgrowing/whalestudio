import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigZeroCayley
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.ReproCoreStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.SchurB

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace NNReal

namespace ReciprocityTheory.ChartRestriction.DS

theorem fdegB_of_isDS {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) (hDS : Formalism.MainNotions.S.IsDS ε lam σ) :
    ∀ μG : Measure (Formalism.QuantumDeterminants.Mt k r), Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG →
      ∃ d : ℝ, Lap.S0.IsFdegB μG (fun g => σ (P * g * P⁻¹)) d := by
  intro μG hH
  have hCay := hP.1
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hCay.1
  obtain ⟨d, hd0, hF⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS lam σ hDS
  have hmap := Lap.haarMap k r ε P hCay
  obtain ⟨c, hc, hμ⟩ := Lap.haarUniq2 k r _ _ μG (Lap.closedSubgroups k r 0).1 hmap hH
  have hemb := Lap.SchurBAux.measEmb ε hd
  refine ⟨d / (c : ℝ), div_pos hd0 (by exact_mod_cast hc), fun v w v' w' => ?_⟩
  have hint := (hF v w v' w').1
  have hval := (hF v w v' w').2
  have hcomp : (fun x : Formalism.QuantumDeterminants.Mt k r =>
        ⟪w, σ (P * Matrix.of x * P⁻¹) v⟫_ℂ * star ⟪w', σ (P * Matrix.of x * P⁻¹) v'⟫_ℂ) ∘
      (fun g : Formalism.REAL.UJ ε =>
        ((P⁻¹ * Formalism.MainNotions.S.umat g * P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
          Formalism.QuantumDeterminants.Mt k r)) =
      fun g => Formalism.MainNotions.S.coefOn σ v w g * star (Formalism.MainNotions.S.coefOn σ v' w' g) := by
    funext g
    show ⟪w, σ (P * (P⁻¹ * Formalism.MainNotions.S.umat g * P) * P⁻¹) v⟫_ℂ *
        star ⟪w', σ (P * (P⁻¹ * Formalism.MainNotions.S.umat g * P) * P⁻¹) v'⟫_ℂ =
      ⟪w, σ (Formalism.MainNotions.S.umat g) v⟫_ℂ * star ⟪w', σ (Formalism.MainNotions.S.umat g) v'⟫_ℂ
    rw [Lap.SchurBAux.conj_cancel' hd]
  have hI : ∫ x : Formalism.QuantumDeterminants.Mt k r,
        ⟪w, σ (P * Matrix.of x * P⁻¹) v⟫_ℂ * star ⟪w', σ (P * Matrix.of x * P⁻¹) v'⟫_ℂ
          ∂(Measure.map (β := Formalism.QuantumDeterminants.Mt k r) (fun g : Formalism.REAL.UJ ε =>
            ((P⁻¹ * Formalism.MainNotions.S.umat g * P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
              Formalism.QuantumDeterminants.Mt k r)) (Formalism.REAL.muG ε)) =
      ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ) := by
    rw [hemb.integral_map, ← hval]
    exact congrArg (fun f => ∫ g, f g ∂(Formalism.REAL.muG ε)) hcomp
  have hIi : Integrable (fun x : Formalism.QuantumDeterminants.Mt k r =>
        ⟪w, σ (P * Matrix.of x * P⁻¹) v⟫_ℂ * star ⟪w', σ (P * Matrix.of x * P⁻¹) v'⟫_ℂ)
      (Measure.map (β := Formalism.QuantumDeterminants.Mt k r) (fun g : Formalism.REAL.UJ ε =>
        ((P⁻¹ * Formalism.MainNotions.S.umat g * P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
          Formalism.QuantumDeterminants.Mt k r)) (Formalism.REAL.muG ε)) := by
    rw [hemb.integrable_map_iff, hcomp]
    exact hint
  rw [hμ]
  refine ⟨hIi.smul_measure_nnreal, ?_⟩
  calc _ = c • (⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)) := by
        rw [integral_smul_nnreal_measure]; exact congrArg (c • ·) hI
    _ = _ := by
        rw [NNReal.smul_def, Complex.real_smul]; push_cast; rw [div_div_eq_mul_div]; ring

end ReciprocityTheory.ChartRestriction.DS
