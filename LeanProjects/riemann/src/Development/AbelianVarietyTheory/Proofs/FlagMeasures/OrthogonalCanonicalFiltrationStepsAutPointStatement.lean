import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalCanonicalFiltrationStepsAutPoint
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.HarderNarasimhan.ShiftInvariance
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonal_canonicalFiltration_steps_autPoint : ∀ (I : AutInst) (x : I.GA), ht (bas I) (frm I x) (lamX I x) = 1 ∧ (1 ≤ I.n → largestSize (bas I) (frm I x) (lamX I x) = (least I x)⁻¹) ∧ (∀ t : ℝ, 0 < t → perpIn I x (stepLe I x t) = stepLt I x t⁻¹ ∧ perpIn I x (stepLt I x t) = stepLe I x t⁻¹) ∧ ∀ S S' : Submodule (𝓞 I.E) (Fin I.n → I.E), IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) S → IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) S' → S ≤ S' → IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (perpIn I x S) ∧ rkK (perpIn I x S) + rkK S = I.n ∧ perpIn I x (perpIn I x S) = S ∧ perpIn I x S' ≤ perpIn I x S ∧ htQ (bas I) (frm I x) (perpIn I x S) (perpIn I x S') = (htQ (bas I) (frm I x) S' S)⁻¹ := by
  first | exact @GlobalTheory.Count.PerpStep.main | exact GlobalTheory.Count.PerpStep.main | (intros; apply GlobalTheory.Count.PerpStep.main <;> assumption)
