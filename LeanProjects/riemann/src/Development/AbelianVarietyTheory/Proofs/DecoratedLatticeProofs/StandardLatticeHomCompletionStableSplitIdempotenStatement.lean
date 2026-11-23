import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardLatticeHomCompletionStableSplitIdempoten
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TiedAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorOneApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardLatticeHomCompletion_stable_splitIdempotent : ∀ (D : D7) (S T : HSp D) (a : AE D), IsSplitIdem D a → ∀ u ∈ stdHom S T, u.map (fun x => a * x) ∈ stdHom S T := by
  first | exact @GlobalTheory.AdForm.stdHom_map_splitIdem | exact GlobalTheory.AdForm.stdHom_map_splitIdem | (intros; apply GlobalTheory.AdForm.stdHom_map_splitIdem <;> assumption)
