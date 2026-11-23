import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisActionRootsOfUnity
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
theorem _root_.GlobalTheory.T.galois_action_roots_of_unity : ∀ (g : ℂ ≃+* ℂ) (k : ℕ), 0 < k → ∃ a : ℤ, IsCoprime a (k : ℤ) ∧
    ∀ n : ℤ, g (Complex.exp (2 * Real.pi * Complex.I * n / k)) = Complex.exp (2 * Real.pi * Complex.I * (a * n) / k) := by
  first | exact @GlobalTheory.cyclotomic_character_of_ringEquiv | exact GlobalTheory.cyclotomic_character_of_ringEquiv | (intros; apply GlobalTheory.cyclotomic_character_of_ringEquiv <;> assumption)
