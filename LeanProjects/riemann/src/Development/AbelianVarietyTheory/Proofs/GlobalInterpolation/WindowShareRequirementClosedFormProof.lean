import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Formalism.SharpRestriction.GrowthBounds.PlaneCountTheoremWithConstants
import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums
import Formalism.SharpRestriction.GrowthBounds.TopChoiceBounds
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TensorOfPairLift

noncomputable section

namespace GlobalTheory.EX.G4

open Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

theorem w_of {eps : ℝ} (Fm : FamP eps) (h13 : FirstTheoremAtFamily Fm) (hLa : 0 < Fm.GK.La) (hCN : CornerGLContinuity.FamilyWindowLogBound Fm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, AuxBlock8.WeightVectorExists (Fm.D x i) (Fm.L x i) (Fm.Gx x i) Fm.GK := by
  have he : 0 < eps := by
    obtain ⟨i⟩ := Fm.Ix_zero
    have := (Fm.L 0 i).sc.eps_pos
    rwa [Fm.L_eps] at this
  obtain ⟨CH, C', b0, b1, b2, b3, b4, b5, b6, hp13⟩ := h13
  obtain ⟨Cm, hCm, h8⟩ := family_first_bound_of_theorem Fm CH C' (kapIDefF Fm) b0 b1 b2 b3 b4 b5 b6 hp13
  obtain ⟨C31, -, h1⟩ := family_first_lemma Fm
  obtain ⟨x0, h⟩ := ((((h1.and (family_orders_bound_of_lemma Fm (TopChoiceBounds.family_band_ratio_holds Fm) hCN)).and
    (family_sizes_bound Fm hLa (eps / 48) (by positivity))).and h8).and (eventually_sizes_admitted Fm)).and (Ev.x1 Fm)
  obtain ⟨x2, H2⟩ := Filter.eventually_atTop.1 (AuxBlock8.Pf.numMean_ev eps Fm.GK Fm.GK_nonneg Cm hCm)
  obtain ⟨x3, H3⟩ := Filter.eventually_atTop.1 (AuxBlock8.Pf.restHypI_ev eps Fm.GK Fm.GK_nonneg Cm C31)
  refine ⟨max x0 (max x2 x3), fun x hx i => ?_⟩
  have e0 : x ≥ x0 := le_trans (le_max_left _ _) hx
  have e2 : x ≥ x2 := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have e3 : x ≥ x3 := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨⟨⟨⟨⟨a1, a4⟩, a5⟩, a8⟩, aSz⟩, hx1⟩ := h x e0 i
  have NM := H2 x e2 (Fm.D x i) (Fm.L x i) (Fm.L_x x i hx1) (Fm.L_eps x i) aSz.1 a5
  have HI := H3 x e3 (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (Fm.L_x x i hx1) (Fm.L_eps x i) aSz a5 a4 a1 NM
  exact AuxBlock8.Pf.weight_condition_of_mean_excess _ _ (AuxBlock8.Pf.meanEx_of (Fm.Gx x i) Fm.GK Fm.GK_nonneg Cm a8 NM HI a4.2.2.1
    (AuxBlock8.Pf.slopeEstimate_of_lemmaB_slopeLine (Fm.Gx x i) Fm.GK Fm.GK_nonneg Cm a8 NM HI a4.2.2.1))

theorem wClosed : DC.WClosed :=
  (((first_theorem_closed_form (fun _ => True) RangeOne.rangeOne_abs).and (signs_closed (fun _ => True))).and
    (TopChoiceBounds.family_log_bound_closed (fun _ => True))).imp fun Fm _ _ h => w_of Fm h.1.1 h.1.2.1 h.2

end GlobalTheory.EX.G4
