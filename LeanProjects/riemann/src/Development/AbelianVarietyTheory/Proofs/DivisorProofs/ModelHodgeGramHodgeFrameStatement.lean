import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelHodgeGramHodgeFrame
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelHodgeGram
open Matrix
open scoped ComplexOrder
open GlobalTheory.HodgeLocGeo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_hodge_gram_hodge_frame : ∀ {ι : Type} [Fintype ι] {p q : ℕ} (U : Set (ι → ℂ)) (Z : (ι → ℂ) → Matrix (Fin p) (Fin q) ℂ), IsOpen U → (∀ a b, DifferentiableOn ℂ (fun x => Z x a b) U) → (∀ x ∈ U, (1 - (Z x)ᴴ * Z x).PosDef) → GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.IsHodgeFrame U (fun x => modelHodgeGram (Z x)) := by
  first | exact @GlobalTheory.HodgeLocGeo.isHodgeFrame_model | exact GlobalTheory.HodgeLocGeo.isHodgeFrame_model | (intros; apply GlobalTheory.HodgeLocGeo.isHodgeFrame_model <;> assumption)
