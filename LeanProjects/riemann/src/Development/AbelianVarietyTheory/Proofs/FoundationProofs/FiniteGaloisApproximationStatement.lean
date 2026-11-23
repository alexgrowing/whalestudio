import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteGaloisApproximation
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_galois_approximation : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ S : Gal p Ω → Finset Ω, ∃ F : Finset (Gal p Ω), ∀ h : Gal p Ω, ∃ g ∈ F, ∀ x ∈ S g, h x = g x := by
  first | exact @GlobalTheory.K5.gal_finite_subcover | exact GlobalTheory.K5.gal_finite_subcover | (intros; apply GlobalTheory.K5.gal_finite_subcover <;> assumption)
