import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmRiemannFormGaloisConjugate
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
theorem _root_.GlobalTheory.T.cm_riemann_form_galois_conjugate : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ g : ℂ ≃+* ℂ, (∀ x, g (io x) = io x) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I]
    (φ : I → E →+* ℂ), (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
    ∀ (n : ℕ) (e : Fin n ≃ I) (h : I → ℝ) (Hm : Matrix (Fin n) (Fin n) ℂ), 0 < n →
      (∀ z : Fin n → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ (Matrix.diagonal fun j ↦ (h (e j) : ℂ)).mulVec (star z)).re) → Hm.IsHermitian →
      (∀ z : Fin n → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) →
      ∃ u ∈ lattice c y, ∃ u' ∈ lattice c y, (∑ i, h i * (φ i u * starRingEnd ℂ (φ i u')).im) ≠ 0 ∧
        0 < (∑ i, h i * (φ i u * starRingEnd ℂ (φ i u')).im) * ((fun j ↦ g (φ (e j) u)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (e j) u'))).im := by
  first | exact @GlobalTheory.ConjRiemannPos.exists_pos_pair | exact GlobalTheory.ConjRiemannPos.exists_pos_pair | (intros; apply GlobalTheory.ConjRiemannPos.exists_pos_pair <;> assumption)
