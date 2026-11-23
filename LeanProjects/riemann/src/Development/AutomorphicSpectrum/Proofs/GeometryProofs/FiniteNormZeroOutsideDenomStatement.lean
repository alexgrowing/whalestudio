import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteNormZeroOutsideDenom
import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ThmFlatA
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FinConstFor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_norm_zero_outside_denom : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c), τ (H.rt : E) = H.rt0 → IsOpen U → U.Nonempty → IsLineFn U τ φ → ∃ n : ℕ, 0 < n ∧ ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (t : ℝ), ¬ (p : ℕ) ∣ n → HasFinNorm U τ φ p κ t → t = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.line_function_norm_zero_away | exact GlobalTheory.CompanionTheory.Ar.Flat.line_function_norm_zero_away | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.line_function_norm_zero_away <;> assumption)
