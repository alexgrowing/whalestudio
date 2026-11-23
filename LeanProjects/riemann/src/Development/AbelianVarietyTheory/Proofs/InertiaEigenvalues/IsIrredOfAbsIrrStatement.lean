import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrredOfAbsIrr
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SemisimplificationConstituents
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIrred_of_absIrr : ∀ {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k), AbsIrrSub ρ ⊤ → GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsIrred (matRep ((Units.coeHom _).comp ρ)) := by
  first | exact @GlobalTheory.IrredOfAbsIrred.isIrred_of_absIrrSub | exact GlobalTheory.IrredOfAbsIrred.isIrred_of_absIrrSub | (intros; apply GlobalTheory.IrredOfAbsIrred.isIrred_of_absIrrSub <;> assumption)
