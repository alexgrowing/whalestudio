import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuleActionFractionField
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.module_action_fraction_field : ∀ (R O : Type) [CommRing R] [CommRing O] (J : Type) [Fintype J] (b : Module.Basis J ℤ O)
    (M : Type) [AddCommGroup M] [Module R M] [Module O M] [SMulCommClass R O M]
    (K : Type) [Field K] [Algebra R K],
    (∀ k : K, ∃ a s : R, algebraMap R K s ≠ 0 ∧ algebraMap R K s * k = algebraMap R K a) →
    ∀ (N : Type) [AddCommGroup N] [Module K N] [Module O N] [SMulCommClass K O N]
    (e : K ⊗[R] M ≃ₗ[K] N),
    (∀ (a : O) (m : M), e (1 ⊗ₜ (a • m)) = a • e (1 ⊗ₜ m)) →
    (letI : Module (K ⊗[ℤ] O) N := TensorProduct.Algebra.module;
      Module.Invertible (K ⊗[ℤ] O) N) →
    ∃ m : M, Function.Bijective
      (Finsupp.linearCombination K (fun i => (1 : K) ⊗ₜ[R] (b i • m))) := by
  first | exact @GlobalTheory.exists_fibre_generator_basis | exact GlobalTheory.exists_fibre_generator_basis | (intros; apply GlobalTheory.exists_fibre_generator_basis <;> assumption)
