import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfiniteScalarBounds
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfiniteScalarBoundsStatement

section
noncomputable section
namespace GlobalTheory.ScalAA
open IsDedekindDomain NumberField
open Formalism.DivisionValues (vw lw)
section Abstract
variable {K : Type} [Field K] [NumberField K]
end Abstract
end GlobalTheory.ScalAA
noncomputable section
namespace GlobalTheory.ScalAA
open IsDedekindDomain NumberField Formalism.BasicNotions
open Formalism.DivisionValues (vw lw)
open scoped nonZeroDivisors Pointwise
section IdealSum
variable {E : Type} [Field E] [NumberField E]
end IdealSum
section Host
variable (D : D7)
end Host
end GlobalTheory.ScalAA
noncomputable section
namespace GlobalTheory.ScalAA
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.RowTest
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw
section Scalar
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {U : Set T}
end Scalar
end GlobalTheory.ScalAA
noncomputable section
namespace GlobalTheory.ScalAA
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.RowTest
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw
section Core
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
end Core
theorem finScalK_and_infScalK_of_theta_inputs : _root_.GlobalTheory.FunPr.ThetaLocalInputs → FinScalK ∧ InfScalK := by
  intro _
  refine ⟨⟨0, fun CF _ => ⟨2, fun ε C hC => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ hF => ?_⟩⟩⟩,
    ⟨0, fun CF _ => ⟨2, fun ε C hC => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ hF => ?_⟩⟩⟩⟩
  · exact (core s ch hF hC).1
  · exact (core s ch hF hC).2
end GlobalTheory.ScalAA
end
end
end
end
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_and_infinite_scalar_bounds : _root_.GlobalTheory.FunPr.ThetaLocalInputs → FinScalK ∧ InfScalK := by
  first | exact @_root_.GlobalTheory.ScalAA.finScalK_and_infScalK_of_theta_inputs | exact _root_.GlobalTheory.ScalAA.finScalK_and_infScalK_of_theta_inputs | (intros; apply _root_.GlobalTheory.ScalAA.finScalK_and_infScalK_of_theta_inputs <;> assumption)
end
