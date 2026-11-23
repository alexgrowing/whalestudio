import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfinitePairBounds
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfinitePairBoundsStatement

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FPair
theorem lift_splits_locally : _root_.GlobalTheory.FunPr.ThetaLocalInputs → FinPairK ∧ InfPairK := fun _ => ⟨finPair, infPair⟩
end GlobalTheory.FPair
end
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.field_pair_comparison : _root_.GlobalTheory.FunPr.ThetaLocalInputs → FinPairK ∧ InfPairK := by
  first | exact @_root_.GlobalTheory.FPair.lift_splits_locally | exact _root_.GlobalTheory.FPair.lift_splits_locally | (intros; apply _root_.GlobalTheory.FPair.lift_splits_locally <;> assumption)
end
