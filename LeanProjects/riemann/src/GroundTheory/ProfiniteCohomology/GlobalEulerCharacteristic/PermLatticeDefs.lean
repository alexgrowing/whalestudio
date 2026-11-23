import Mathlib
import GroundTheory.GlobalFields.HerbrandQuotients.SUnitsPerm
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

abbrev funPermAction (Γ X A : Type*) [Group Γ] [MulAction Γ X] [AddCommGroup A] :
    DistribMulAction Γ (X → A) where
  smul γ f x := f (γ⁻¹ • x)
  one_smul f := funext fun x => show f ((1 : Γ)⁻¹ • x) = f x by rw [inv_one, one_smul]
  mul_smul γ δ f := funext fun x =>
    show f ((γ * δ)⁻¹ • x) = f (δ⁻¹ • γ⁻¹ • x) by rw [mul_inv_rev, mul_smul]
  smul_zero γ := rfl
  smul_add γ f f' := rfl

end GroundTheory.ProfCoh
