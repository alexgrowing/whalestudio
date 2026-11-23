import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyInNormalAt
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TorusAlgebraicHolds

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.KeyOfPeriod

theorem exists_keyIn_classicalFrame :
    ∀ (g : ℕ) (τ₀ : Matrix (Fin g) (Fin g) ℂ) (a₀ b₀ : Fin g → ℂ), 1 ≤ g → τ₀.IsSymm → (τ₀.map Complex.im).PosDef → (∀ i, a₀ i = 0 ∨ a₀ i = 1 / 2) → (∀ i, b₀ i = 0 ∨ b₀ i = 1 / 2) → ∃ (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L x.P.g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ), τ = τ₀.submatrix (Fin.cast h) (Fin.cast h) ∧ (a = fun i => a₀ (i.cast h)) ∧ (b = fun i => b₀ (i.cast h)) ∧ τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ (∀ i, a i = 0 ∨ a i = 1 / 2) ∧ (∀ i, b i = 0 ∨ b i = 1 / 2) ∧ (∀ z, z ∈ u.Λ ↔ ∃ m n : Fin x.P.g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) ∧ u.IsRig x.rig ∧ u.IsFn x.th (thetaChar τ a b) ∧ (∀ i, u.IsDiff (Pi.single i (2 * Real.pi * Complex.I)⁻¹) (x.v i)) := by
  intro g τ₀ a₀ b₀ hg hs hp ha hb
  obtain ⟨x, h, hx⟩ := exists_keyIn_normalAt GlobalTheory.thetaUnifAV_all GlobalTheory.torusAlgebraic_holds g τ₀ a₀ b₀ hg hs hp
    ⟨ha, hb⟩
  obtain ⟨u, h₁, h₂, h₃, h₄, h₅, h₆⟩ := (GlobalTheory.KeyPow.normalAt_one_iff x _ _ _).1 hx
  exact ⟨x, h, u, _, _, _, rfl, rfl, rfl, h₁, h₂, fun i => ha _, fun i => hb _, h₃, h₄, h₅, h₆⟩

end GlobalTheory.KeyOfPeriod
