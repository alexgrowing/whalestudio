import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorFractionInjectiveOfTensorInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_fraction_injective_of_tensor_injective : ∀ (R R₁ B K L : Type) [CommRing R] [CommRing R₁] [CommRing B] [Field K] [Field L] [Algebra R R₁] [Algebra R B] [Algebra R K] [Algebra B K] [IsScalarTower R B K] [IsFractionRing B K] (θ : K →+* L) (c : R₁ →+* L) (β : B ⊗[R] R₁ →+ L), Function.Injective β → (∀ b r, β (b ⊗ₜ[R] r) = θ (algebraMap B K b) * c r) → ∀ (n : ℕ) (u : Fin n → K) (r : Fin n → R₁), ∑ j, c (r j) * θ (u j) = 0 → ∑ j, u j ⊗ₜ[R] r j = 0 := by
  first | exact @GlobalTheory.tensor_fraction_injective_of_injective | exact GlobalTheory.tensor_fraction_injective_of_injective | (intros; apply GlobalTheory.tensor_fraction_injective_of_injective <;> assumption)
