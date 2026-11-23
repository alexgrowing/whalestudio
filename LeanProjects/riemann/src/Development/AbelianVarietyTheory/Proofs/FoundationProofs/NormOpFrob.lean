import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBasisOneAddXPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOfRedEqZero
open GlobalTheory.Col PowerSeries

theorem GlobalTheory.Col.normOp_frob : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R), FrobLift R p σ →
    ∀ h : PowerSeries R, ∃ r : PowerSeries R, normOp p h = smap σ h + (p : PowerSeries R) * r := by
  intro R _ p _ σ hfl h
  obtain ⟨b, -⟩ := GlobalTheory.Col.exists_basis_one_add_X_pow R p hfl.complete
  exact GlobalTheory.Col.NormFrob.normOp_eq_smap_add p σ hfl b h
