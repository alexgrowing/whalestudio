import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.HaarExists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigZeroDecay
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCPX

noncomputable section

open Finset MeasureTheory Matrix
open scoped ENNReal

namespace CompanionTheory.RgExh.Dec.L.AB

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool}

theorem one_le_hs (hn : 0 < n) (g : S7.UJ ε) : 1 ≤ Formalism.REAL.hs (S7.toM g) := by
  have hU : (S7.toM g)ᴴ * Jm ε * S7.toM g = Jm ε := g.2
  have hs1 : ∀ a : Fin n, ‖(if ε a = true then (1 : ℂ) else -1)‖ = 1 := by
    intro a
    split <;> simp
  have h00 := congrFun (congrFun hU ⟨0, hn⟩) ⟨0, hn⟩
  rw [Matrix.mul_apply] at h00
  simp only [Jm, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq] at h00
  calc (1 : ℝ) = ‖(if ε ⟨0, hn⟩ = true then (1 : ℂ) else -1)‖ := (hs1 _).symm
    _ = ‖∑ j, star (S7.toM g j ⟨0, hn⟩) * (if ε j = true then (1 : ℂ) else -1) *
          S7.toM g j ⟨0, hn⟩‖ := by rw [h00]
    _ ≤ ∑ j, ‖star (S7.toM g j ⟨0, hn⟩) * (if ε j = true then (1 : ℂ) else -1) *
          S7.toM g j ⟨0, hn⟩‖ := norm_sum_le _ _
    _ = ∑ j, ‖S7.toM g j ⟨0, hn⟩‖ ^ 2 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [norm_mul, norm_mul, norm_star, hs1]
        ring
    _ ≤ ∑ j, ∑ k, ‖S7.toM g j k‖ ^ 2 :=
        Finset.sum_le_sum fun j _ => Finset.single_le_sum (f := fun k => ‖S7.toM g j k‖ ^ 2)
          (fun k _ => by positivity) (Finset.mem_univ _)
    _ = Formalism.REAL.hs (S7.toM g) := rfl

private theorem hs_eq_re_trace_conjTranspose_mul' (X : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.hs X = (Matrix.trace (X * Xᴴ)).re := by
  simp [Formalism.REAL.hs, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

theorem hs_mul_K (X : Matrix (Fin n) (Fin n) ℂ) (k : S7.KG ε) : Formalism.REAL.hs (X * S7.toMK k) = Formalism.REAL.hs X := by
  have hk : S7.toM (k : S7.UJ ε) ∈ Kset ε := k.2
  obtain ⟨hu, -⟩ : S7.toM (k : S7.UJ ε) ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      S7.toM (k : S7.UJ ε) * Jm ε = Jm ε * S7.toM (k : S7.UJ ε) := hk
  have hUU : S7.toMK k * (S7.toMK k)ᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hu
    rwa [Matrix.star_eq_conjTranspose] at this
  rw [hs_eq_re_trace_conjTranspose_mul', hs_eq_re_trace_conjTranspose_mul', Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (S7.toMK k), hUU, Matrix.one_mul]

theorem continuous_aT (A : Matrix (Fin n) (Fin n) ℂ) : Continuous (fun t : ℝ => aT A t) := by
  have h1 : Continuous fun t : ℝ => (t : ℂ) • A := by fun_prop
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
  show Continuous fun t : ℝ => NormedSpace.exp ((t : ℂ) • A)
  exact NormedSpace.exp_continuous.comp h1

end CompanionTheory.RgExh.Dec.L.AB
