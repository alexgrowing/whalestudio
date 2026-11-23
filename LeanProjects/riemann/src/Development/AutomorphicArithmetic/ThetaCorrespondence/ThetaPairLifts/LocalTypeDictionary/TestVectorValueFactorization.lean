import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfinitePsiBounds
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible

section
namespace TestFunctionNorms
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.CoefModel
open Formalism.UG
open scoped ComplexOrder
namespace GlobalTheory.CompanionTheory.TestVal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Lat
variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}
end Lat
section Cast
variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}
end Cast
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
theorem test_value_psi_finite_infinite : _root_.GlobalTheory.FunPr.ThetaLocalInputs → FinPsiK ∧ InfPsiK := by
  intro _
  constructor
  · refine ⟨0, fun CF _ => ⟨0, fun ε C _ => ⟨0, ?_⟩⟩⟩
    intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ _ w c u hu x
    exact pullback_fin_relation _ _ w c u hu x
  · refine ⟨0, fun CF _ => ⟨0, fun ε C _ => ⟨0, ?_⟩⟩⟩
    intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ _ σ c u x
    exact inf_aux _ _ σ c u x
end GlobalTheory.CompanionTheory.TestVal
end
end
end TestFunctionNorms
section
open GlobalTheory.SumSize GlobalTheory.RowClaim
theorem _root_.GlobalTheory.Adopt.test_vector_value_factorization : _root_.GlobalTheory.FunPr.ThetaLocalInputs → FinPsiK ∧ InfPsiK := by
  first | exact @_root_.TestFunctionNorms.GlobalTheory.CompanionTheory.TestVal.test_value_psi_finite_infinite | exact _root_.TestFunctionNorms.GlobalTheory.CompanionTheory.TestVal.test_value_psi_finite_infinite | (intros; apply _root_.TestFunctionNorms.GlobalTheory.CompanionTheory.TestVal.test_value_psi_finite_infinite <;> assumption)
end
end
