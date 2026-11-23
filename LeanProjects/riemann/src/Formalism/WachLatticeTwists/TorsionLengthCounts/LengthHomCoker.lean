import Formalism.WachLatticeTwists.StatementDual
import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthKerOfDetEqZero
import Formalism.CharacterColumnKernels.IdempotentNormalForms.SingleEqSmul

open Module IsDiscreteValuationRing Formalism.NG

noncomputable section

namespace Formalism.RepresentationBoundsCohomology

namespace FlowLoadBounds

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

lemma mem_annKO {H : Type*} [AddCommGroup H] [Module O H] (S : Submodule O H)
    (φ : H →ₗ[O] KO O) : φ ∈ annKO O S ↔ ∀ x ∈ S, φ x = 0 := Iff.rfl

section Res

variable {H : Type*} [AddCommGroup H] [Module O H]

def resQ (I M : Submodule O H) : annKO O I →ₗ[O] ((M ⧸ I.comap M.subtype) →ₗ[O] KO O) where
  toFun φ := (I.comap M.subtype).liftQ ((φ : H →ₗ[O] KO O) ∘ₗ M.subtype)
    (fun x hx => LinearMap.mem_ker.mpr ((mem_annKO I φ.1).mp φ.2 (x : H) hx))
  map_add' φ ψ := by ext x; rfl
  map_smul' c φ := by ext x; rfl

end Res

end FlowLoadBounds

end Formalism.RepresentationBoundsCohomology
