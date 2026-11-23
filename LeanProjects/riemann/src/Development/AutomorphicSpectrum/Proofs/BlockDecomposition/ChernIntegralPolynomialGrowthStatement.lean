import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralPolynomialGrowth
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsPresents
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_integral_polynomial_growth : ∀ (Y : Var ℂ) (Δ Δ₀ : Y.Dv) (L L₀ : LB Y.X) (r : L.ι → Y.Fnˣ) (r₀ : L₀.ι → Y.Fnˣ), Presents Δ L r → Presents Δ₀ L₀ r₀ → ∀ (φ : Weight Y.str (RingHom.id ℂ) L) (φ₀ : Weight Y.str (RingHom.id ℂ) L₀), φ.IsCInf → φ₀.IsCInf → ∃ P : Polynomial ℝ, P.natDegree ≤ Y.dim ∧ ∀ m : ℕ, ∃ (L' : LB Y.X) (r' : L'.ι → Y.Fnˣ) (ψ : Weight Y.str (RingHom.id ℂ) L'), Presents (Δ + m • Δ₀) L' r' ∧ ψ.IsCInf ∧ ψ.chernInt Y.dim Set.univ (fun _ => 1) = P.eval (m : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.ChernTwist.chernInt_twist_polynomial | exact GlobalTheory.CompanionTheory.ChernTwist.chernInt_twist_polynomial | (intros; apply GlobalTheory.CompanionTheory.ChernTwist.chernInt_twist_polynomial <;> assumption)
