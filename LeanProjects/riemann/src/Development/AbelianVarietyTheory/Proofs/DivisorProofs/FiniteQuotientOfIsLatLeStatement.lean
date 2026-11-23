import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteQuotientOfIsLatLe
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAddFundamentalDomainLatticeDomain
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_quotient_of_isLat_le' : ∀ {g : ℕ} (M M' : Submodule ℤ (Fl g)), IsLat M → IsLat M' → M ≤ M' → Finite (↥M' ⧸ M.submoduleOf M') := by
  first | exact @GlobalTheory.finite_quotient_of_isLat_le | exact GlobalTheory.finite_quotient_of_isLat_le | (intros; apply GlobalTheory.finite_quotient_of_isLat_le <;> assumption)
