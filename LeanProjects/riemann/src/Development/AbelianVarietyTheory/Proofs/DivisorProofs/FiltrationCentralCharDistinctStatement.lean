import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltrationCentralCharDistinct
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothDetPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filtration_central_char_distinct : ∀ {G V Y : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G V) (τ : Representation ℂ G Y) (N : ℕ) (S : Fin (N + 1) → Subrepresentation ρ),
    Monotone S → S 0 = ⊥ → S (Fin.last N) = ⊤ →
    (∀ t t' : Fin N, t ≠ t' →
      (∃ (z : G) (c c' : ℂ), c ≠ c' ∧ (∀ y, τ z y = c • y) ∧ ∀ y, subQuot (S t.succ) (S t.castSucc) z y = c' • y) ∨
      (∃ (z : G) (c c' : ℂ), c ≠ c' ∧ (∀ y, τ z y = c • y) ∧ ∀ y, subQuot (S t'.succ) (S t'.castSucc) z y = c' • y)) →
    (∀ t : Fin N, HomLeOne (subQuot (S t.succ) (S t.castSucc)) τ) → HomLeOne ρ τ := by
  first | exact @GlobalTheory.FiltLevi.homLeOne_of_filtration | exact GlobalTheory.FiltLevi.homLeOne_of_filtration | (intros; apply GlobalTheory.FiltLevi.homLeOne_of_filtration <;> assumption)
