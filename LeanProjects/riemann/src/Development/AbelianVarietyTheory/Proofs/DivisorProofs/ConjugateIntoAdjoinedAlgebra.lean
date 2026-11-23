import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartRingLocalizationMembership
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_into_adjoined_algebra : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (δ : GL (Fin n) F') (γ : GL (Fin n) F), IsNorm s δ γ → ∃ y : GL (Fin n) F', ((y⁻¹ * δ * galAct F F' n s y : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} ∧ nrm s (y⁻¹ * δ * galAct F F' n s y) = incl F F' n γ := by
  first | (exact @GlobalTheory.Shin.isNorm_exists_twistedConj_adjoin) | (exact GlobalTheory.Shin.isNorm_exists_twistedConj_adjoin) | (intros; apply GlobalTheory.Shin.isNorm_exists_twistedConj_adjoin  <;> assumption)
