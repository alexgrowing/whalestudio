import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterInvariantAdelicFormEqMulEvalZero

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

namespace PositivityTheory.SiegelWeilFormula.Ald.PCI

def FinPart : Prop := ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
  ∀ (κ' κ'' : Type) [Fintype κ'] [Fintype κ''] (a : ((κ' ⊕ κ'' → Af F) → ℂ) →ₗ[ℂ] ℂ),
    (∀ (y : κ'' → Af F), ∀ g ∈ SB (κ' ⊕ κ'' → Af F),
      a (fun x => ψ (pairA F 0 ((x ∘ Sum.inr) ⬝ᵥ y)) * g x) = a g) →
    ∀ g ∈ SB (κ' ⊕ κ'' → Af F), (∀ x' : κ' → Af F, g (Sum.elim x' 0) = 0) → a g = 0

end PositivityTheory.SiegelWeilFormula.Ald.PCI

end
