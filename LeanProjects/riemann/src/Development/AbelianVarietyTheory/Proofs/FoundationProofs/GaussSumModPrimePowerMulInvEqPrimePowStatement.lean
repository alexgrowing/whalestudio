import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussSumModPrimePowerMulInvEqPrimePow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ChSumSubCMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSubOnePowThreeLe
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussSumModPrimePower_mul_inv_eq_prime_pow : ∀ (l : ℕ) [Fact l.Prime] (m : ℕ) (z : Qbar l) (ψ : DirichletCharacter (Qbar l) (l ^ m)), IsPrimitiveRoot z (l ^ m) → ψ.IsPrimitive → gSum m z ψ * gSum m z⁻¹ ψ⁻¹ = (l : Qbar l) ^ m := by
  first | exact @GlobalTheory.KZ.Cmp.gSum_mul_gSum_inv_prim | exact GlobalTheory.KZ.Cmp.gSum_mul_gSum_inv_prim | (intros; apply GlobalTheory.KZ.Cmp.gSum_mul_gSum_inv_prim; all_goals assumption)
