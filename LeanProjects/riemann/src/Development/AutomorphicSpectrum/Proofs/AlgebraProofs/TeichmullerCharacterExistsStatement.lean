import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterExists
open scoped Matrix TensorProduct
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.teichmuller_character_exists : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∃ σ : MulChar F R, (∀ a b, σ (a + b) - σ a - σ b ∈ Ideal.span {(p : R)}) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.fund_ex_relay | exact GlobalTheory.CompanionTheory.Ar.GR.fund_ex_relay | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.fund_ex_relay <;> assumption)
