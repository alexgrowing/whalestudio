import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.RootSumWOff

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)

def sgnV (v : InfinitePlace G.F) : ℂ := if v.embedding (L.e (D.ω : D.F)) = D.ρc then 1 else -1

abbrev Arch (G : HTGroup p) : Type := InfinitePlace G.F → Fin G.n → ℂ

def hv {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) : ℂ := star y ⬝ᵥ (M *ᵥ x)

structure ArchFrame where
  th : VQ D →+ Arch G
  r : InfinitePlace G.F → ℝ
  r_pos : ∀ v, 0 < r v
  act : ∀ (c : G.C) w v, th (L.rep c w) v = G.psi v c *ᵥ th w v
  form : ∀ u w, ((D.EF.baseChange ℚ u w : ℚ) : ℝ) = ∑ v, r v * (-(sgnV L v) * Complex.I * hv (G.gram v) (th u v) (th w v)).re
  span : Submodule.span ℝ (Set.range th) = ⊤
  dim : Module.finrank ℝ (Arch G) = Module.finrank ℚ (VQ D)
  dimg : Module.finrank ℝ (Arch G) = 2 * D.g

def IsFMat (kp : VQ D ≃+ (Fin G.n → G.F)) (σ : G.C ≃ₐ[G.F] Matrix (Fin G.n) (Fin G.n) G.F) : Prop :=
  ∀ c w, kp (L.rep c w) = σ c *ᵥ kp w

def IsPosJ {n : ℕ} (M J : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) : Prop :=
  J * J = -1 ∧ Jᴴ * M * J = M ∧ ∀ x, x ≠ 0 → 0 < (-s * Complex.I * hv M (J *ᵥ x) x).re

end UpperTheory.Gal.W2
