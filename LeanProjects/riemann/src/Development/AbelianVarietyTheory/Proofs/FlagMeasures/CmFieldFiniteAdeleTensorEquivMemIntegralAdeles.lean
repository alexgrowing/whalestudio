import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsReductionActionChosenPlaces
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RedBasicsPf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodAtReductionConjugatedUnitaryElement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAddEquivOfCard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeSelfDualHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WBEqPrimeComap
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommTensCastRSymmMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SurjectiveReductionOntoFiniteLevelGroup
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

open IsDedekindDomain

namespace GlobalTheory.FixedConj

theorem comm_tensCastR_symm_mem_intAf {E : Type} [Field E] [NumberField E] {F₁ F₂ : Subfield E} (h : F₁ = F₂)
    (x : E ⊗[F₂] FiniteAdeleRing (𝓞 F₂) F₂)
    (hx : x ∈ Subring.closure ({x | ∃ y : 𝓞 E, x = (y : E) ⊗ₜ[F₂] (1 : FiniteAdeleRing (𝓞 F₂) F₂)} ∪
      {x | ∃ a : FiniteAdeleRing (𝓞 F₂) F₂, (∀ v, a v ∈ v.adicCompletionIntegers F₂) ∧ x = (1 : E) ⊗ₜ[F₂] a})) :
    (Algebra.TensorProduct.comm (↥F₁) (FiniteAdeleRing (𝓞 F₁) F₁) E).toRingEquiv
      ((GlobalTheory.StdFrame.tensCastR h).symm x) ∈ Formalism.L2.Herm.intAf (↥F₁) E := by
  subst h
  have hS : Subring.closure ({x | ∃ y : 𝓞 E, x = (y : E) ⊗ₜ[F₁] (1 : FiniteAdeleRing (𝓞 F₁) F₁)} ∪
      {x | ∃ a : FiniteAdeleRing (𝓞 F₁) F₁, (∀ v, a v ∈ v.adicCompletionIntegers F₁) ∧ x = (1 : E) ⊗ₜ[F₁] a}) ≤
      (Formalism.L2.Herm.intAf (↥F₁) E).comap
        (((GlobalTheory.StdFrame.tensCastR (rfl : F₁ = F₁)).symm.trans
          (Algebra.TensorProduct.comm (↥F₁) (FiniteAdeleRing (𝓞 F₁) F₁) E).toRingEquiv : _ ≃+* _) : _ →+* _) := by
    rw [Subring.closure_le]
    rintro z (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
    · show (Algebra.TensorProduct.comm (↥F₁) (FiniteAdeleRing (𝓞 F₁) F₁) E)
          ((Algebra.TensorProduct.comm (↥F₁) (FiniteAdeleRing (𝓞 F₁) F₁) E).symm ((y : E) ⊗ₜ[F₁] 1)) ∈ _
      rw [AlgEquiv.apply_symm_apply]
      exact Subring.subset_closure (Or.inl ⟨⟨(y : E), ⟨y, rfl⟩⟩, rfl⟩)
    · show (Algebra.TensorProduct.comm (↥F₁) (FiniteAdeleRing (𝓞 F₁) F₁) E)
          ((Algebra.TensorProduct.comm (↥F₁) (FiniteAdeleRing (𝓞 F₁) F₁) E).symm ((1 : E) ⊗ₜ[F₁] a)) ∈ _
      rw [AlgEquiv.apply_symm_apply]
      exact Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
  exact hS hx

theorem adeleEquiv_mem_intAf : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (a : ReciprocityTheory.Aut.AL D.host.E),
    a ∈ ReciprocityTheory.Aut.ALint D.host.E → GlobalTheory.FixedConj.adeleEquiv D hF a ∈ Formalism.L2.Herm.intAf (↥D.host.F) D.host.E := by
  intro D hF a ha
  exact comm_tensCastR_symm_mem_intAf hF a ha

end GlobalTheory.FixedConj
