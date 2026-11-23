import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfSurjectiveProjectiveConstRank
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_of_surjective_projective_constRank : ∀ (B M : Type) [CommRing B] [AddCommGroup M] [Module B M] (g : ℕ) (f : M →ₗ[B] (Fin g → B)), Module.Finite B M → Module.Projective B M → (∀ p : PrimeSpectrum B, Module.rankAtStalk M p = g) → Function.Surjective f → Function.Injective f := by
  first | exact @GlobalTheory.CechPer.injective_of_surjective_of_rankAtStalk_eq | exact GlobalTheory.CechPer.injective_of_surjective_of_rankAtStalk_eq | (intros; apply GlobalTheory.CechPer.injective_of_surjective_of_rankAtStalk_eq <;> assumption)
