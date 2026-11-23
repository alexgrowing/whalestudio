import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RepresentativeValuesVectorVariationUnipotentOrbi
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsProjOnOne
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representativeValuesVector_variation_unipotentOrbit : ∀ (B : RowsAut) (b ρ M : ℝ) (P : ℕ) (D : ℕ) (T : Fin D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund)) (Fr : Fin D → B.Hs → B.I.GA → ℂ) (x : B.I.GA) (W : Submodule B.I.E (Fin B.I.n → B.I.E)), StepBoundAt B b P → (∀ i, IsReps B (T i) (Fr i)) → 0 ≤ M → (∀ y ∈ omega B.I x W ρ, ∀ u ∈ VP B (P + 1), ‖vv B Fr u y‖ ≤ M * ‖u‖) → ∀ y ∈ omega B.I x W ρ, ∀ u ∈ VP B P, ‖vv B Fr u y - vv B Fr u x‖ ≤ ρ * Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖ := by
  first | exact @GlobalTheory.PathVar.path_variation | exact GlobalTheory.PathVar.path_variation | (intros; apply GlobalTheory.PathVar.path_variation <;> assumption)
