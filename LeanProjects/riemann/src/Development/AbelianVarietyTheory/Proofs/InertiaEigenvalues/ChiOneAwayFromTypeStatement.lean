import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChiOneAwayFromType
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.JumpDictionary
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chi_one_away_from_type : GlobalTheory.Published.FontaineBcris → ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm2 D → SumRepresentations.adm5 D → GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.BlockCharParam D → GlobalTheory.HubX.MuUnr D → ∀ i : D.nd.Loc, D.nd.l i ∉ TwistedPlaces.gset D → GlobalTheory.PtCore.ChiOneE D i := by
  first | exact @GlobalTheory.ChiOneNoPt.main | exact GlobalTheory.ChiOneNoPt.main | (intros; apply GlobalTheory.ChiOneNoPt.main <;> assumption)
