import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassFieldFinrankPowPrincipal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeNormOfKummer
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rayClassField_finrank_pow_principal : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (𝔮 : Ideal (𝓞 K)), IsRayField K L 𝔮 → ∀ I : Ideal (𝓞 K), I ≠ ⊥ → IsCoprime I 𝔮 → ∃ α β : 𝓞 K, RayPair 𝔮 α β ∧ I ^ Module.finrank K L * Ideal.span {β} = Ideal.span {α} := by
  first | exact @GlobalTheory.Mem.Fld.RayExp.pow_finrank_principal | exact GlobalTheory.Mem.Fld.RayExp.pow_finrank_principal | (intros; apply GlobalTheory.Mem.Fld.RayExp.pow_finrank_principal <;> assumption)
