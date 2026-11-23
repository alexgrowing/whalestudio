import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DetUpMatSub

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

theorem dl_diagonal {r : ℕ} (c : Fin (r + 1) → ℂ) (l : ℕ) (h : l ≤ r + 1) :
    Dl (Matrix.diagonal c) l = ∏ i : Fin l, c (Fin.castLE h i) := by
  unfold Dl
  simp only [dif_pos h, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective h), Matrix.det_diagonal,
    Function.comp_apply]

theorem continuous_dl {r : ℕ} (l : ℕ) : Continuous fun Z : MZ r => Dl (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) l := by
  unfold Dl
  by_cases h : l ≤ r + 1
  · simp only [dif_pos h]
    fun_prop
  · simp only [dif_neg h]
    exact continuous_const

theorem continuous_gv {r : ℕ} (T T' : ℝ) : Continuous fun Z : MZ r => Gv T T' (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) := by
  have h1 := continuous_dl (r := r) (r + 1)
  have h2 := continuous_dl (r := r) r
  unfold Gv
  fun_prop

theorem continuous_diag (r : ℕ) : Continuous fun c : Fin (r + 1) → ℂ => (Matrix.diagonal c : MZ r) := by
  exact Continuous.matrix_diagonal continuous_id

theorem measurable_wt (r k : ℕ) (T T' : ℝ) : Measurable fun c : Fin (r + 1) → ℂ => wtLoc k T T' c := by
  have h1 : Continuous fun c : Fin (r + 1) → ℂ => Gv T T' (Matrix.diagonal c : MZ r) :=
    (continuous_gv T T').comp (continuous_diag r)
  have h2 := h1.measurable
  have h3 : ∀ l, Measurable fun c : Fin (r + 1) → ℂ => Dl (Matrix.diagonal c : MZ r) l :=
    fun l => ((continuous_dl l).comp (continuous_diag r)).measurable
  unfold wtLoc
  unfold JacV
  unfold modC
  fun_prop

theorem dcLoc_eq (r : ℕ) : dcLoc (r := r) = (2 : ℝ≥0∞) ^ (r + 1) • (volume : Measure (Fin (r + 1) → ℂ)) := by
  haveI : SigmaFinite ((2 : ℝ≥0∞) • (volume : Measure ℂ)) := by rw [two_smul]; infer_instance
  unfold dcLoc
  refine Measure.pi_eq fun s _ => ?_
  rw [Measure.smul_apply, volume_pi, Measure.pi_pi, smul_eq_mul]
  simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
