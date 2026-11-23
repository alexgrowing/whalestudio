import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipLatStmt
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfApproxFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfMain

noncomputable section

open Matrix NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.Unip Formalism.L2.SG.TermOp.Vanish

namespace Formalism.L2.SG.Pf.UnipB

theorem latStep_lvl {D : D7} (X : HidaSetting D) (tY : ℕ) (htY : 0 < tY) (k : ℕ) :
    ∃ C : ℝ, ∀ P : InfinitePlace X.B.I.F → Matrix (Kap X) (Kap X) ℂ,
      (∀ v, InPat (lvk X) (k + 1) (P v)) → (∀ v, (P v)ᴴ * JBv X v = -(JBv X v * P v)) →
      ∃ Y : Matrix (Kap X) (Kap X) X.B.I.E, InPat (lvk X) (k + 1) Y ∧ Yᴴ * JB X = -(JB X * Y) ∧ IntDiv tY Y ∧
        ∀ v i j, ‖(P v - Y.map (X.B.I.φ v)) i j‖ ≤ C := by
  obtain ⟨C, hC⟩ := ratApprox_holds D X 1 (Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J).one_mem (k + 1) (by omega) tY htY
  have hG1 : Gr X (↑(1 : GL (Fin X.B.I.n) X.B.I.E) : Matrix _ _ _) = 1 := by
    rw [Units.val_one]; exact rcm_gr_one X
  have hG1' : Gr X (↑(1 : GL (Fin X.B.I.n) X.B.I.E)⁻¹ : Matrix _ _ _) = 1 := by
    rw [inv_one]; exact hG1
  refine ⟨C, fun P hPk hPs => ?_⟩
  obtain ⟨Y, hYk, -, hYs, ⟨A, hA⟩, hYC⟩ := hC P fun v => ⟨hPk v, by
    rw [hG1, hG1', Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, Matrix.mul_one]
    exact inPat_mono (by omega) (hPk v), hPs v⟩
  refine ⟨Y, hYk, hYs, ⟨A.map (fun a => (a : X.B.I.E)), fun i j => RingOfIntegers.isIntegral_coe (A i j), hA⟩,
    fun v i j => ?_⟩
  have := hYC v i j
  rw [Matrix.sub_apply] at this ⊢
  rwa [norm_sub_rev]

theorem latStep_holds {D : D7} (X : HidaSetting D) : LatStepP X := by
  intro tY htY
  choose C hC using latStep_lvl X tY htY
  refine ⟨∑ j ∈ Finset.range (N0 D), |C j|, Finset.sum_nonneg fun j _ => abs_nonneg _, fun k hk P hPk hPs => ?_⟩
  by_cases hkN : k < N0 D
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨Y, hY1, hY2, hY3, hY4⟩ := hC j P hPk hPs
    refine ⟨Y, hY1, hY2, hY3, fun v i l => (hY4 v i l).trans ((le_abs_self _).trans ?_)⟩
    exact Finset.single_le_sum (f := fun j => |C j|) (fun j _ => abs_nonneg _) (Finset.mem_range.2 (by omega))
  · have hP0 : ∀ v, P v = 0 := fun v =>
      eq_zero_of_inPat (L := k) (fun i => by have := lvk_lt X i; omega) (hPk v)
    refine ⟨0, inPat_zero _, by simp, intDiv_zero _, fun v i j => ?_⟩
    rw [hP0 v]
    simp only [Matrix.map_zero _ (map_zero _), sub_zero, Matrix.zero_apply, norm_zero]
    exact Finset.sum_nonneg fun j _ => abs_nonneg _

theorem latStepC_holds : LatStepC := fun _ X => latStep_holds X

end Formalism.L2.SG.Pf.UnipB
