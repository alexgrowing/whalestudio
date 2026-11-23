import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerTraceAlmostSurjective
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicTower_trace_almost_surjective : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (L : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l)), Kinf K ≤ L → (∀ h ∈ Hinf K, ∀ x ∈ L, h x ∈ L) → (∀ s ∈ S, s ∈ Hinf K) → (∀ h ∈ Hinf K, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ L.fixingSubgroup) → ∀ a : Om l, a ∈ Kinf K → ‖a‖ < 1 → ∃ b : Om l, b ∈ L ∧ ‖b‖ ≤ 1 ∧ ∑ s ∈ S, s b = a := by
  first | exact @GlobalTheory.Cyc.trace_almost_onto | exact GlobalTheory.Cyc.trace_almost_onto | (intros; apply GlobalTheory.Cyc.trace_almost_onto <;> assumption)
