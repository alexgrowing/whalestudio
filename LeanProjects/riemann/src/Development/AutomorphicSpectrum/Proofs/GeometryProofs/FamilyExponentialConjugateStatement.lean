import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyExponentialConjugate
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DifferentiableOnStarStar
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.family_exponential_conjugate : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (ρ : ℝ) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e' : Flat.FamExp G M (Metric.ball 0 ρ) (Flat.Conj.conjPts ψ)), ∃ e : Flat.FamExp G M (Metric.ball 0 ρ) ψ, ∀ b p, p ∈ e.per b ↔ star p ∈ e'.per (star b) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ConjExp.exists_famExp_of_conj | exact GlobalTheory.CompanionTheory.Ar.Flat.ConjExp.exists_famExp_of_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ConjExp.exists_famExp_of_conj <;> assumption)
