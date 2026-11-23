import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthQuotientSmulLeFinrankOfEmbedding
import Mathlib
open Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_quotient_smul_le_finrank_of_embedding : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K] (W M : Type) [AddCommGroup W] [Module K W] [Module O W] [IsScalarTower O K W] [FiniteDimensional K W] [AddCommGroup M] [Module O M] (f : M →ₗ[O] W), Function.Injective f → ∀ a : O, Module.length O (M ⧸ LinearMap.range (a • (LinearMap.id : M →ₗ[O] M))) ≤ (Module.finrank K W : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
  first | exact @GlobalTheory.length_quotient_smul_range_le_finrank_mul | exact GlobalTheory.length_quotient_smul_range_le_finrank_mul | (intros; apply GlobalTheory.length_quotient_smul_range_le_finrank_mul <;> assumption)
