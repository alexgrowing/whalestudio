import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFiltrationSizeProperties
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.HarderNarasimhan.ShiftInvariance
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalLatticeFiltration_size_properties : ∀ (I : AutInst) (x : I.GA) (t : ℝ), 0 < t → IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (stepLe I x t) ∧ IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (stepLt I x t) ∧ stepLt I x t ≤ stepLe I x t ∧ (∀ t', t < t' → stepLe I x t ≤ stepLt I x t') ∧ (stepLe I x t ≠ ⊥ → largestSize (bas I) (frm I x) (stepLe I x t) ≤ t) ∧ (stepLt I x t ≠ ⊥ → largestSize (bas I) (frm I x) (stepLt I x t) < t) ∧ (∀ N, stepLe I x t < N → N ≤ lamX I x → t < sizeQ (bas I) (frm I x) N (stepLe I x t)) ∧ (∀ N, stepLt I x t < N → N ≤ lamX I x → t ≤ sizeQ (bas I) (frm I x) N (stepLt I x t)) ∧ (1 ≤ I.n → 0 < least I x ∧ (stepLe I x t = ⊥ ↔ t < least I x) ∧ (stepLt I x t = ⊥ ↔ t ≤ least I x)) := by
  first | exact @GlobalTheory.CountSteps.steps | exact GlobalTheory.CountSteps.steps | (intros; apply GlobalTheory.CountSteps.steps <;> assumption)
