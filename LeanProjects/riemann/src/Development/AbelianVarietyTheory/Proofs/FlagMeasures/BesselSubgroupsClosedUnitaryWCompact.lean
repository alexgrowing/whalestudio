import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SymmetricMeasureL2NormEqResolutionL2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem isClosedSub_of_closedSubgroup {k r : ℕ} {S : Set (Mat k r)} (hG : S ⊆ GG k r)
    (h : Formalism.FourierDecayAlt.B2.IsClosedSubgroup S) : IsClosedSub k r S :=
  ⟨hG, h.closed, h.one_mem, h.mul_mem, h.inv_mem⟩

theorem closedSub_groups : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    IsClosedSub k r (GG k r) ∧ IsClosedSub k r (Nset k r) ∧ IsClosedSub k r (UWset k r z) ∧
      IsClosedSub k r (Sset k r z) ∧ IsCompact (UWset k r z) := by
  intro k r z hz hT
  have cG : Formalism.FourierDecayAlt.B2.IsClosedSubgroup (GG k r) := Formalism.FourierDecayAlt.P.B2x2.closedG k r
  have cN : Formalism.FourierDecayAlt.B2.IsClosedSubgroup (Nset k r) := Formalism.FourierDecayAlt.P.B2x2.closedN k r
  have cW : Formalism.FourierDecayAlt.B2.IsClosedSubgroup (UWset k r z) := Formalism.FourierDecayAlt.P.B2x3.closedW k r z
  have sN : Nset k r ⊆ GG k r := fun g hg => hg.1
  have sW : UWset k r z ⊆ GG k r := fun g hg => hg.1
  have sS : Sset k r z ⊆ GG k r := by
    rintro s ⟨h, hh, n, hn, rfl⟩
    exact cG.mul_mem _ (sW hh) _ (sN hn)
  exact ⟨isClosedSub_of_closedSubgroup subset_rfl cG, isClosedSub_of_closedSubgroup sN cN,
    isClosedSub_of_closedSubgroup sW cW,
    isClosedSub_of_closedSubgroup sS (GlobalTheory.BesselPeriodCompare.closedS hz),
    Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r z hz hT⟩

end GlobalTheory.SgInf
