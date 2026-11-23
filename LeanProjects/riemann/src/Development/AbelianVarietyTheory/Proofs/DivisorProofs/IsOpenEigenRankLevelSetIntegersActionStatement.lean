import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenEigenRankLevelSetIntegersAction
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigRank
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
theorem _root_.GlobalTheory.T.isOpen_eigenRank_levelSet_integersAction : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (F : IntermediateField ℚ ℂ) (hF : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ F) (R : Type) [CommRing R] (iF : F →+* R) (n : ℕ) (A : 𝓞 E → Matrix (Fin n) (Fin n) R), A 1 = 1 → (∀ a b, A (a + b) = A a + A b) → (∀ a b, A (a * b) = A a * A b) → ∀ (τ : E →+* ℂ) (N : ℕ), IsOpen {𝔭 : PrimeSpectrum R | GlobalTheory.BalProj.eigRank (algebraMap R 𝔭.asIdeal.ResidueField) A (GlobalTheory.BalProj.embR F hF iF τ) = N} := by
  first | exact @GlobalTheory.BalProjOpen.isOpen_eigRank_eq | exact GlobalTheory.BalProjOpen.isOpen_eigRank_eq | (intros; apply GlobalTheory.BalProjOpen.isOpen_eigRank_eq <;> assumption)
