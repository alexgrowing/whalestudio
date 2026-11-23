import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCoprimeLatticeMultiplier
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
theorem _root_.GlobalTheory.T.norm_coprime_lattice_multiplier : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (t : (Af K)ˣ) (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
    ∀ k : ℕ, 0 < k → ∃ (m : K) (b : ℕ), 0 < b ∧ Nat.Coprime b k ∧ Complex.normSq (io m) = b / modF t ∧
      ∀ u ∈ lattice c (y * (upIdele K E t)⁻¹), algebraMap K E m * u ∈ lattice c y ∧
        ((upIdele K E t : Af E) * algebraMap E (Af E) (u / k) - algebraMap E (Af E) (algebraMap K E m * u / k)) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c := by
  first | exact @GlobalTheory.ConjApprox.approx_idele | exact GlobalTheory.ConjApprox.approx_idele | (intros; apply GlobalTheory.ConjApprox.approx_idele <;> assumption)
