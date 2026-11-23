import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeSpansRealSpace
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
theorem _root_.GlobalTheory.T.cm_lattice_spans_real_space : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), 0 < d → δ ^ 2 = -(d : K) →
    ∀ g : ℂ ≃+* ℂ, (∀ x, g (io x) = io x) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) →
      ∀ (n : ℕ) (e : Fin n ≃ I) (Λ : Submodule ℤ (Fin n → ℂ)) (L : Set E),
        Submodule.span ℝ (Λ : Set (Fin n → ℂ)) = ⊤ → (∀ w, w ∈ Λ ↔ ∃ x ∈ L, w = fun j ↦ g (φ (e j) x)) →
      ∀ (h : I → ℝ) (β : E), (∀ i, (h i : ℂ) = 2 * Complex.I * φ i β) → ∀ N : ℝ, 0 < N →
      ∀ Hm : Matrix (Fin n) (Fin n) ℂ, Hm.IsHermitian →
        (∀ x ∈ L, ∀ x' ∈ L, ((fun j ↦ g (φ (e j) x)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (e j) x'))).im =
          N⁻¹ * ∑ i, h i * (φ i x * starRingEnd ℂ (φ i x')).im) →
        ∃ h' : I → ℝ, Hm = Matrix.diagonal (fun j ↦ (h' (e j) : ℂ)) ∧
          ∀ i, g ((h i : ℂ) * (Real.sqrt d : ℝ)) = (N : ℂ) * ((h' i : ℂ) * (Real.sqrt d : ℝ)) := by
  first | exact @GlobalTheory.HermDiagCM.diagonal_of_conj_form | exact GlobalTheory.HermDiagCM.diagonal_of_conj_form | (intros; apply GlobalTheory.HermDiagCM.diagonal_of_conj_form <;> assumption)
