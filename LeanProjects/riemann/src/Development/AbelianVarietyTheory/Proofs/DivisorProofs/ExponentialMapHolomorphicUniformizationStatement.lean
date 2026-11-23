import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentialMapHolomorphicUniformization
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponential_map_holomorphic_uniformization : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (z : Sp ℂ ⟶ X) (g : ℕ) (ex : (Fin g → ℂ) → (Over.mk z ⟶ t.G)), IsExpAt t z ex → IsHolTo Set.univ (fun w => (ex w).left) → ∀ (φ : Fib ℂ) (m : CubeMap φ.G t.G), FibAt t z φ m → ∀ (n : ℕ), φ.P.g = n → ∀ (u : HolUnif φ.P.A φ.P.L n) (Hm : Matrix (Fin n) (Fin n) ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ → ∃ π : (Fin g → ℂ) →ₗ[ℂ] (Fin n → ℂ), (∀ (w : Fin g → ℂ) (v' : epsR ℂ ⟶ φ.G) (W : Fin n → ℂ), IsDerivAt0 (fun s => (ex s).left) w (v'.left ≫ m.F) → u.IsDiff W (v' ≫ φ.q) → W = π w) ∧ Submodule.span ℝ (π '' {w | ex w = 1}) = ⊤ ∧ Module.finrank ℝ (Submodule.span ℝ {w | ex w = 1}) + Module.finrank ℂ (LinearMap.ker π) ≤ 2 * g ∧ ∀ (k : ℕ) (v w : Fin g → ℂ) (ζ : ℂˣ), 0 < k → ex v = 1 → ex w = 1 → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm (π v) (π w)).im : ℂ) / k) → GlobalTheory.UU.CubWeil t.cub k (ex ((k : ℂ)⁻¹ • v)) (ex ((k : ℂ)⁻¹ • w)) (unitOn ζ) := by
  first | exact @GlobalTheory.FibExpAb.exists_linear_to_abelian_part | exact GlobalTheory.FibExpAb.exists_linear_to_abelian_part | (intros; apply GlobalTheory.FibExpAb.exists_linear_to_abelian_part <;> assumption)
