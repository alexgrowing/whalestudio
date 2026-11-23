import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorRestrictionSubMemIdealMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylor_restriction_sub_mem_ideal_map : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R) (π : R →ₐ[ℂ] ℂ), (∀ i, π (t i) = 0) → ∀ (W : Opens (Tot I g)) (W₀ : Opens (Tot Empty g)), (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) → ∀ ρ : Hol W →+* R ⊗[ℂ] Hol W₀, IsTay N t ρ → ∀ (h : Hol W) (h₀ : Hol W₀), (∀ p ∈ W₀, h₀.fn p = h.fn (0, p.2)) → ρ h - 1 ⊗ₜ[ℂ] h₀ ∈ (RingHom.ker π).map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol W₀) := by
  first | exact @GlobalTheory.AnPer.taylor_reduces_to_slice | exact GlobalTheory.AnPer.taylor_reduces_to_slice | (intros; apply GlobalTheory.AnPer.taylor_reduces_to_slice <;> assumption)
