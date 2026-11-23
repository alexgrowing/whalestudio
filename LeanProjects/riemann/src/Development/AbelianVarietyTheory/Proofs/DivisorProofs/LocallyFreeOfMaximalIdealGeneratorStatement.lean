import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyFreeOfMaximalIdealGenerator
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_free_of_maximal_ideal_generator : ∀ (R O : Type) [CommRing R] [CommRing O] (J : Type) [Fintype J] (b : Module.Basis J ℤ O)
    (M : Type) [AddCommGroup M] [Module R M] [Module O M] [SMulCommClass R O M],
    (∀ p : Ideal R, p.IsMaximal → ∃ g : R, g ∉ p ∧ ∃ m : M,
      (∀ x : M, ∃ (n : ℕ) (c : J →₀ R), g ^ n • x = Finsupp.linearCombination R (fun i => b i • m) c) ∧
      (∀ c : J →₀ R, Finsupp.linearCombination R (fun i => b i • m) c = 0 → ∃ n : ℕ, g ^ n • c = 0)) →
    letI : Module (R ⊗[ℤ] O) M := TensorProduct.Algebra.module
    Module.Invertible (R ⊗[ℤ] O) M := by
  first | exact @GlobalTheory.InvGlue.invertible_of_locally_singly_generated | exact GlobalTheory.InvGlue.invertible_of_locally_singly_generated | (intros; apply GlobalTheory.InvGlue.invertible_of_locally_singly_generated <;> assumption)
