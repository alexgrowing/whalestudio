import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardOrdinaryLocalConditionModPrimePowLeConstMul
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousMatQApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SelNZero
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_ordinaryLocalConditionModPrimePow_le_const_mul : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ (c : Coef l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1), ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ v : S, IsPlaceOver A v.1 → Nat.card (Lc c n W hint S hN A v) ≤ C * Nat.card (Qn c n) := by
  first | exact @GlobalTheory.Ord2.GwIneq.CardOrd.card_ord | exact GlobalTheory.Ord2.GwIneq.CardOrd.card_ord | (intros; apply GlobalTheory.Ord2.GwIneq.CardOrd.card_ord <;> assumption)
