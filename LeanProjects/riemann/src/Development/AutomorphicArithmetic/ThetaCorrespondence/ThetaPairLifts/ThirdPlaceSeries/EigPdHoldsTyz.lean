import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenPeriodOfLocalGlobal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeCharEqOfLAdicRealisation

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TameEig
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition Topology
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}
abbrev _root_.GlobalTheory.TameEig.eigPd_holds_tyz : Prop :=  ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.AdmAAlt D → _root_.GlobalTheory.StringRepresentationDecomposition.LocalGlobalCompatible D → RbEx D → EigPd D
end GlobalTheory.TameEig
end
end
