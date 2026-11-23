import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSectionSqSmooth
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_section_sq_smooth : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s → A.Smooth (fun y => normSec L s y ^ 2) := by
  first | exact @GlobalTheory.SmoothNormSq.normSec_sq_smooth | exact GlobalTheory.SmoothNormSq.normSec_sq_smooth | (intros; apply GlobalTheory.SmoothNormSq.normSec_sq_smooth <;> assumption)
