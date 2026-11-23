import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TrivialLocalCondition
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.DistinctAbsIrredConstituents

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace Formalism.MainNotions.AdmissibleParameterJ
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual NumberField IsDedekindDomain
variable {D : D7}
section Sets
variable (D)
end Sets
section Emb
variable (D)
variable {D}
end Emb
section Stmt
variable (D)
variable {D} (L : SizeData₂ D)
end Stmt
section admitted
variable (D)
def DeRhamFamilyAwayAlt : Prop := ∀ i r, GoodR D.nd i r → _root_.UpperTheory.GalS.G2a D.nd D.naut i r
variable {D} (L : SizeData₂ D)
def AdmJAlt : Prop :=
  _root_.Formalism.MainNotions.AdmissibleParameterJ.DeRhamFamilyAwayAlt D ∧ CrysIffWD D.nd D.naut ∧ _root_.UpperTheory.GalS.DeRhamJumpsDistinctCondition D ∧ AdmDict D ∧ AdmRead D ∧ AdmPar L
variable (D) in
def JumpClosed : Prop := ∀ L : SizeData₂ D, _root_.Formalism.MainNotions.AdmissibleParameterJ.AdmJAlt L → JumpConditions L
end admitted
end Formalism.MainNotions.AdmissibleParameterJ
end
end
