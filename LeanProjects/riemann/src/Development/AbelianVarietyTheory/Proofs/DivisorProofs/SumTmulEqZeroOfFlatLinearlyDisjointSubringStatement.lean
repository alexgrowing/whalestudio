import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTmulEqZeroOfFlatLinearlyDisjointSubring
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_tmul_eq_zero_of_flat_linearlyDisjoint_subring : ∀ (R R₁ A F K : Type) [CommRing R] [CommRing R₁] [CommRing A] [Field F] [Field K] [Algebra R A] [Algebra R R₁], Module.Flat R R₁ → ∀ (c₀ : R →+* F) (e : A →+* F) (c : R₁ →+* K) (θ : F →+* K), Function.Injective c₀ → Function.Injective e → e.comp (algebraMap R A) = c₀ → θ.comp c₀ = c.comp (algebraMap R R₁) → LinDisj c₀ c θ → ∀ (n : ℕ) (a : Fin n → A) (r : Fin n → R₁), ∑ i, θ (e (a i)) * c (r i) = 0 → ∑ i, a i ⊗ₜ[R] r i = 0 := by
  first | exact @GlobalTheory.Desc.tmul_sum_eq_zero_of_flat_linDisj | exact GlobalTheory.Desc.tmul_sum_eq_zero_of_flat_linDisj | (intros; apply GlobalTheory.Desc.tmul_sum_eq_zero_of_flat_linDisj <;> assumption)
