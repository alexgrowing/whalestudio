import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricChartDerivationBoundaryParamMemSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricChart_derivation_boundaryParam_mem_span : ∀ (A : Type) [CommRing A] (k : Type) [Field k] (m d : ℕ) (ψ : A →+* ChartRing k m d) (δ : Derivation ℤ A A) (D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (I : Ideal A), (∀ a ∈ I, δ a ∈ I) → (∀ a, D' (ψ a) = ψ (δ a)) → I.map ψ = Ideal.span {∏ i, bdParam k m d i} → ∀ i, D' (bdParam k m d i) ∈ Ideal.span {bdParam k m d i} := by
  first | exact @GlobalTheory.ChartDerBd.deriv_bdParam_mem_span | exact GlobalTheory.ChartDerBd.deriv_bdParam_mem_span | (intros; apply GlobalTheory.ChartDerBd.deriv_bdParam_mem_span <;> assumption)
