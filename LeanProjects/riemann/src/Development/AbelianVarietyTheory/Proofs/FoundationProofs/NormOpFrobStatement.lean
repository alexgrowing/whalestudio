import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormOpFrob
import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
open GlobalTheory.Col PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normOp_eq_smap_add_mul : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R), FrobLift R p σ → ∀ h : PowerSeries R, ∃ r : PowerSeries R, normOp p h = smap σ h + (p : PowerSeries R) * r := by
  first | exact @GlobalTheory.Col.normOp_frob | exact GlobalTheory.Col.normOp_frob | (intros; apply GlobalTheory.Col.normOp_frob <;> assumption)
