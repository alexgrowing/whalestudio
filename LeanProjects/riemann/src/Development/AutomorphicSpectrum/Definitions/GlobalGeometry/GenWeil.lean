import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.MemEigSpOfMemHtDual

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

structure GenWeil (G : Over X) [GrpObj G] (L : LB G.left) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (n : ℕ)
    (e : (Over.mk ξ ⟶ G) → (Over.mk ξ ⟶ G) → Ωˣ) : Prop where
  finite : Finite {x : Over.mk ξ ⟶ G // x ^ n = 1}
  mul_left : ∀ x x' g, x ^ n = 1 → x' ^ n = 1 → g ^ n = 1 → e (x * x') g = e x g * e x' g
  mul_right : ∀ x g g', x ^ n = 1 → g ^ n = 1 → g' ^ n = 1 → e x (g * g') = e x g * e x g'
  perfect : ∀ χ : (Over.mk ξ ⟶ G) → Ωˣ, (∀ g g', g ^ n = 1 → g' ^ n = 1 → χ (g * g') = χ g * χ g') →
    ∃ x, x ^ n = 1 ∧ ∀ g, g ^ n = 1 → χ g = e x g
  nondeg : ∀ g, g ^ n = 1 → (∀ x, x ^ n = 1 → e x g = 1) → g = 1
  weil : ∀ x g, x ^ n = 1 → g ^ n = 1 → ∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k)
    (xk gk : Over.mk (spMap i ≫ ξ) ⟶ G) (c : kˣ), xk.left = spMap i ≫ x.left → gk.left = spMap i ≫ g.left →
      (Out.WeilIs G L n xk gk (unitOn c) ↔ (c : k) = i (e x g))

end GlobalTheory.CompanionTheory.Ar
