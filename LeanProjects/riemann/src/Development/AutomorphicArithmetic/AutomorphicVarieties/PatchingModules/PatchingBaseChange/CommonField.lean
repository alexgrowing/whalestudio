import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CommonField
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.common_field :
    ∀ (B κ₁ κ₂ : Type) [CommRing B] [Field κ₁] [Field κ₂] (f₁ : B →+* κ₁) (f₂ : B →+* κ₂), RingHom.ker f₁ = RingHom.ker f₂ → ∃ (κ : Type) (_ : Field κ) (j₁ : κ₁ →+* κ) (j₂ : κ₂ →+* κ), j₁.comp f₁ = j₂.comp f₂ :=
  _root_.UpperTheory.Reformulated.B.Qe15.common_field
