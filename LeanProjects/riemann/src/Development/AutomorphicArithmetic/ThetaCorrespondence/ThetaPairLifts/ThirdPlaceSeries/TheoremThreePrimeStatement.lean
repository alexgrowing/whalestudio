import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleThreePrime
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AdmissibleResidualTameEigenvalues

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace Formalism.MainNotions.AdmissibleThreePrime
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
def Adm3PVariant (D : D7) : Prop := SumRepresentations.tieLab D ∧ _root_.UpperTheory.GalS.AdmissibleResidualTameEigenvalues D
def ThreePrimeTheoremStatement (D : D7) : Prop := _root_.Formalism.MainNotions.AdmissibleThreePrime.Adm3PVariant D → TheoremThreePrime D
end Formalism.MainNotions.AdmissibleThreePrime
end
end
