import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTaylorAlgHomHolomorphicNilpotent
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_taylor_algHom_holomorphic_nilpotent : ∀ {I : Type} [Fintype I] [DecidableEq I] {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (V : Opens (I → ℂ)), 0 ∈ V → ∃ θ : Hol V →ₐ[ℂ] R, ∀ f, θ f = taylor N t f.fn := by
  first | exact @GlobalTheory.AnPer.exists_taylor_algHom | exact GlobalTheory.AnPer.exists_taylor_algHom | (intros; apply GlobalTheory.AnPer.exists_taylor_algHom <;> assumption)
