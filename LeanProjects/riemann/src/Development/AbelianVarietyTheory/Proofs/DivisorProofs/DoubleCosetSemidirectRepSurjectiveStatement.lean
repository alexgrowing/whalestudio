import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetSemidirectRepSurjective
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleCoset_semidirect_rep_surjective : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ (TM CM : Subgroup M) (TP CP : Subgroup P), CM ≤ TM → (∀ p, p ∈ TP ↔ ∃ t ∈ TM, s t = p) → (∀ p, p ∈ CP ↔ ∃ t ∈ CM, s t = p) → (∀ q : M, TM ⊓ KM.map (MulAut.conj q).toMonoidHom ≤ CM) → ∀ d : DoubleCoset.Quotient (TP : Set P) (KP : Set P), ∃ X : N, DoubleCoset.mk TP KP (s (Quotient.out (DoubleCoset.mk TM KM (π (Quotient.out d)))) * u X) = d := by
  first | exact @GlobalTheory.doubleCoset_semidirect_surj | exact GlobalTheory.doubleCoset_semidirect_surj | (intros; apply GlobalTheory.doubleCoset_semidirect_surj <;> assumption)
