import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuleActionOfFieldFibres
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.module_action_of_field_fibres : ∀ (R O : Type) [CommRing R] [CommRing O] [Module.Free ℤ O] [Module.Finite ℤ O] (M : Type)
    [AddCommGroup M] [Module R M] [Module O M] [SMulCommClass R O M] [Module.Finite R M] [Module.Projective R M],
    (∀ (K : Type) [Field K] [Algebra R K], ∃ (N : Type) (_ : AddCommGroup N) (_ : Module K N) (_ : Module O N)
      (_ : SMulCommClass K O N) (e : K ⊗[R] M ≃ₗ[K] N),
      (∀ (a : O) (m : M), e (1 ⊗ₜ (a • m)) = a • e (1 ⊗ₜ m)) ∧
      letI : Module (K ⊗[ℤ] O) N := TensorProduct.Algebra.module
      Module.Invertible (K ⊗[ℤ] O) N) →
    letI : Module (R ⊗[ℤ] O) M := TensorProduct.Algebra.module
    Module.Invertible (R ⊗[ℤ] O) M := by
  first | exact @GlobalTheory.invertible_of_fibres_invertible | exact GlobalTheory.invertible_of_fibres_invertible | (intros; apply GlobalTheory.invertible_of_fibres_invertible <;> assumption)
