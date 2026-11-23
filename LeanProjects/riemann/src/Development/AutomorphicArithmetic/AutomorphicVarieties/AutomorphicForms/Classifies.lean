import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CongruenceNumberRankThree

noncomputable section

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N

namespace UpperTheory.V.Af

structure TrData (q e : ℕ) where

  S : Type
  fin : Finite S

  t : S → ℂ
  conj : ∀ σ : ℂ ≃+* ℂ, ∃ u : S ≃ S, ∀ s, t (u s) = σ (t s)
  bd : ∀ s, ‖t s‖ ≤ 3
  int : ∀ s, IsIntegral ℤ ((q : ℂ) ^ e * t s)

instance {q e : ℕ} : Inhabited (TrData q e) :=
  ⟨⟨Empty, inferInstance, fun s => s.elim, fun _ => ⟨.refl _, fun s => s.elim⟩, fun s => s.elim, fun s => s.elim⟩⟩

namespace TrData

variable {q e : ℕ}

def Classifies {Γ : Type} [Group Γ] {l : ℕ} [Fact l.Prime] (D : TrData q e) (ι : Qbar l ≃+* ℂ) (g : Γ)
    (admitted : (Γ →* GL (Fin 3) (Qbar l)) → Prop) : Prop :=
  ∃ cl : {r // admitted r} → D.S, (∀ r r', cl r = cl r' → RepIso r.1 r'.1) ∧
    ∀ r, (r.1 g : Matrix (Fin 3) (Fin 3) (Qbar l)).trace = ι.symm (D.t (cl r))

def sum (D D' : TrData q e) : TrData q e where
  S := D.S ⊕ D'.S
  fin := by have := D.fin; have := D'.fin; infer_instance
  t := Sum.elim D.t D'.t
  conj σ := by
    obtain ⟨u, hu⟩ := D.conj σ
    obtain ⟨u', hu'⟩ := D'.conj σ
    exact ⟨u.sumCongr u', fun s => by cases s <;> simp [hu, hu']⟩
  bd s := by cases s; exacts [D.bd _, D'.bd _]
  int s := by cases s; exacts [D.int _, D'.int _]

theorem card_sum (D D' : TrData q e) : Nat.card (D.sum D').S = Nat.card D.S + Nat.card D'.S := by
  have := D.fin; have := D'.fin
  exact Nat.card_sum

theorem Classifies.sum {Γ : Type} [Group Γ] {l : ℕ} [Fact l.Prime] {D D' : TrData q e} {ι : Qbar l ≃+* ℂ} {g : Γ}
    {P P' : (Γ →* GL (Fin 3) (Qbar l)) → Prop} (h : D.Classifies ι g P) (h' : D'.Classifies ι g P') :
    (D.sum D').Classifies ι g fun r => P r ∨ P' r := by
  classical
  obtain ⟨cl, h1, h2⟩ := h
  obtain ⟨cl', h1', h2'⟩ := h'
  let F : {r // P r ∨ P' r} → D.S ⊕ D'.S :=
    fun r => if hr : P r.1 then Sum.inl (cl ⟨r.1, hr⟩) else Sum.inr (cl' ⟨r.1, r.2.resolve_left hr⟩)
  have e1 : ∀ r (hr : P r.1), F r = Sum.inl (cl ⟨r.1, hr⟩) := fun r hr => dif_pos hr
  have e2 : ∀ r (hr : ¬ P r.1), F r = Sum.inr (cl' ⟨r.1, r.2.resolve_left hr⟩) := fun r hr => dif_neg hr
  refine ⟨F, fun r r' (H : F r = F r') => ?_, fun r => ?_⟩
  · by_cases hr : P r.1 <;> by_cases hr' : P r'.1
    · rw [e1 r hr, e1 r' hr'] at H; exact h1 _ _ (Sum.inl.inj H)
    · rw [e1 r hr, e2 r' hr'] at H; cases H
    · rw [e2 r hr, e1 r' hr'] at H; cases H
    · rw [e2 r hr, e2 r' hr'] at H; exact h1' _ _ (Sum.inr.inj H)
  · change _ = ι.symm (Sum.elim D.t D'.t (F r))
    by_cases hr : P r.1
    · rw [e1 r hr]; exact h2 ⟨r.1, hr⟩
    · rw [e2 r hr]; exact h2' ⟨r.1, _⟩

end TrData

end UpperTheory.V.Af
