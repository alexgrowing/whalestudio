import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChiGrid

theorem sig_X'_eq_sig_Y (D : D7) (τ : D.host.E →+* ℂ) : D.sp.X'.sig τ = (D.sp.Y D.R.m).sig τ := by
  have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := D.sp.cm.cmUnram.2.1 τ
  have hw : (Matrix.of fun i j => (D.sp.Y D.R.m).hT (D.sp.eYm (D.sp.X'.frame i)) (D.sp.eYm (D.sp.X'.frame j))) =
      D.sp.X'.gram := by
    exact Matrix.ext fun i j => D.sp.eYm_isom _ _
  have hs := D.sp.X'_sig τ
  rw [← hw] at hs
  have k := sig_family (D.sp.Y D.R.m) τ hτ _ hs (D.sp.Y_sig D.R.m τ)
  have h3 := sig_sum _ D.sp.X'_sig τ
  have h4 := sig_sum _ (D.sp.Y_sig D.R.m) τ
  have hYr : (D.sp.Y D.R.m).rank = D.sp.X'.rank := by
    rw [D.sp.Y_rank D.R.m le_rfl, D.sp.X'_rank]; rfl
  rw [hYr] at k h4
  exact Prod.ext (by omega) (by omega)

theorem colY_isV : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → ∀ j, j ≤ D.R.m → (columnBlock L j).IsV (rankV D 0 j) ((D.R.m - j) / 2) := by
  intro D T L μ0 hL j hj
  have hr : rankV D 0 j = D.R.rankY j := by
    simp only [rankV, zero_mul, add_zero]; rfl
  rw [hr]
  rcases hj.eq_or_lt with rfl | hlt
  · rw [colY_m]
    refine ⟨D.sp.X'_rank, D.sp.X'_sig, fun τ => ?_,
      GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hL.βX⟩
    exact (sig_X'_eq_sig_Y D τ).trans (D.Y_sigval _ le_rfl τ)
  · rw [colY_lt L hlt]
    have e : min j D.R.m = j := min_eq_left hj
    refine ⟨?_, D.sp.Y_sig _, fun τ => ?_,
      GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βY j hlt)⟩
    · exact (D.sp.Y_rank _ (min_le_right _ _)).trans (by rw [e])
    · exact (D.Y_sigval _ (min_le_right _ _) τ).trans (by rw [e]; rfl)

end GlobalTheory.ChiGrid
