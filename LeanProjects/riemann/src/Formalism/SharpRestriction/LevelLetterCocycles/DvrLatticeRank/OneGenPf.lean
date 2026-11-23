import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantUniformizer
import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf

noncomputable section

namespace Formalism.MainNotions.N.Ln34.OneGenPf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem onegen_pf : Formalism.MainNotions.N.Ln34.OneGenStep := by
  intro D HW F Cm CA CB CK _ l _ _ K LL hG
  obtain ⟨-, -, e, -, hspan, hφ, hγ⟩ := Formalism.MainNotions.LiftingTheory.liftb_HOne_holds D HW F l K 1 LL hG
  exact ⟨e, hspan, hφ, hγ⟩

end Formalism.MainNotions.N.Ln34.OneGenPf
