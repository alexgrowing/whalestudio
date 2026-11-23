import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionRatioDetermined
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_function_ratio_determined : ∀ (S : Type) (f f' : S → ℝ) (A : ℝ), 0 < A → (∀ s, ∃ n : ℤ, f' s = n) →
    (∀ k : ℕ, 0 < k → ∃ (a : ℤ) (b : ℕ), 0 < b ∧ Nat.Coprime b k ∧ IsCoprime a (k : ℤ) ∧
      ∀ s, (∃ n : ℤ, (b : ℝ) / A * f s = n) ∧ ∃ n : ℤ, f' s - a * ((b : ℝ) / A * f s) = k * n) →
    (∃ s, f s ≠ 0 ∧ 0 < f s * f' s) → ∀ s, f' s = f s / A := by
  first | exact @GlobalTheory.ConjArith.form_eq_div | exact GlobalTheory.ConjArith.form_eq_div | (intros; apply GlobalTheory.ConjArith.form_eq_div <;> assumption)
