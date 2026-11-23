import Mathlib

namespace Formalism.CohomologicalDescent

open CoxeterSystem

universe u v

def InvSeqAll : Prop :=
  ∀ (B : Type u) (W : Type v) [Group W] (M : CoxeterMatrix B) (cs : CoxeterSystem M W) (w₀ : W),
    (∀ w : W, cs.length w ≤ cs.length w₀) →
    ∀ ω : List B, cs.IsReduced ω → cs.wordProd ω = w₀ →
      (cs.rightInvSeq ω).Nodup ∧ (∀ t : W, t ∈ cs.rightInvSeq ω ↔ cs.IsReflection t) ∧
      (cs.leftInvSeq ω).Nodup ∧ (∀ t : W, t ∈ cs.leftInvSeq ω ↔ cs.IsReflection t) ∧
      ω.length = Nat.card {t : W // cs.IsReflection t}

def adjSwap {n : ℕ} (a : Fin n) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.swap a.castSucc a.succ

def wordPerm {n : ℕ} (ω : List (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  (ω.map adjSwap).prod

def rightInvSeqA {n : ℕ} : List (Fin n) → List (Equiv.Perm (Fin (n + 1)))
  | [] => []
  | a :: ω => (wordPerm ω)⁻¹ * adjSwap a * wordPerm ω :: rightInvSeqA ω

def InvSeqAllTypeA : Prop :=
  ∀ (n : ℕ) (ω : List (Fin n)), wordPerm ω = Fin.revPerm →
    (∀ ω' : List (Fin n), wordPerm ω' = Fin.revPerm → ω.length ≤ ω'.length) →
      (rightInvSeqA ω).Nodup ∧
      (∀ t : Equiv.Perm (Fin (n + 1)),
        t ∈ rightInvSeqA ω ↔ ∃ i j : Fin (n + 1), i < j ∧ t = Equiv.swap i j) ∧
      ω.length = (n + 1).choose 2

def InvSeqOddTypeA : Prop :=
  ∀ (n : ℕ) (ω : List (Fin n)), wordPerm ω = Fin.revPerm →
    (∀ i j : Fin (n + 1), i < j → Odd ((rightInvSeqA ω).count (Equiv.swap i j))) ∧
      (n + 1).choose 2 ≤ ω.length

end Formalism.CohomologicalDescent
