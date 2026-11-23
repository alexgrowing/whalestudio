import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula

namespace GlobalTheory.FlagZ.Count

theorem card_sub_prod {ι β : Type} (p : β → Prop) :
    Nat.card {x : ι × β // p x.2} = Nat.card ι * Nat.card {y : β // p y} := by
  rw [← Nat.card_prod]
  exact Nat.card_congr ⟨fun x => (x.1.1, ⟨x.1.2, x.2⟩), fun x => ⟨(x.1, x.2.1), x.2.2⟩, fun _ => rfl, fun _ => rfl⟩

theorem below_full {ι : Type} {N : ℕ} (τ : ι) (i j : Fin N) :
    Below (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd τ i j ↔ j < i :=
  ⟨fun ⟨_, _, h₁, h₂⟩ => h₁.trans_le h₂, fun h => ⟨(τ, j.succ), rfl, by simp, by simpa using h⟩⟩

theorem card_lt (N : ℕ) : Nat.card {y : Fin N × Fin N // y.2 < y.1} = N * (N - 1) / 2 := by
  have h := Fintype.card_product_filter_lt (α := (Fin N)ᵒᵈ)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← Nat.choose_two_right]
  rw [Fintype.card_orderDual, Fintype.card_fin] at h
  exact h

theorem card_full (ι : Type) [Fintype ι] (N : ℕ) :
    Nat.card {x : ι × Fin N × Fin N // x.2.2 < x.2.1} = dimFl ι N := by
  rw [card_sub_prod (fun y : Fin N × Fin N => y.2 < y.1), card_lt, Nat.card_eq_fintype_card, dimFl]

theorem card_block (N : ℕ) (j : Fin (N + 1)) :
    Nat.card {y : Fin N × Fin N // (y.2 : ℕ) < j ∧ (j : ℕ) ≤ y.1} = j * (N - j) := by
  have hj := j.is_le
  have e : {y : Fin N × Fin N // (y.2 : ℕ) < j ∧ (j : ℕ) ≤ y.1} ≃ Fin j × Fin (N - j) :=
    ⟨fun y => (⟨y.1.2, y.2.1⟩, ⟨y.1.1 - j, by have := y.1.1.2; have := y.2.2; omega⟩),
      fun z => ⟨(⟨z.2 + j, by have := z.2.2; omega⟩, ⟨z.1, by have := z.1.2; omega⟩), z.1.2, by simp⟩,
      fun y => by
        have := y.2.2
        ext <;> simp
        omega,
      fun z => by ext <;> simp⟩
  rw [Nat.card_congr e]
  simp

theorem card_cellVar (ι : Type) [Fintype ι] (N : ℕ) :
    Nat.card (CellVar (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd) = dimFl ι N ∧
    (∀ j : Fin (N + 1), Nat.card (CellVar (id : ι → ι) (fun _ => j)) = dimGr ι N j) ∧
    ∀ x : ι × Fin (N + 1), 0 < (x.2 : ℕ) → (x.2 : ℕ) < N →
      Nat.card (CellVar (fun y : {y // y ≠ x} => y.1.1) (fun y => y.1.2)) + 1 = dimFl ι N := by
  refine ⟨?_, fun j => ?_, fun x h0 hN => ?_⟩
  · rw [← card_full]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => below_full _ _ _)
  · rw [dimGr, ← card_block, ← Nat.card_eq_fintype_card,
      ← card_sub_prod (fun y : Fin N × Fin N => (y.2 : ℕ) < j ∧ (j : ℕ) ≤ y.1)]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun y =>
      ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨y.1, rfl, h⟩⟩)
  · rw [← card_full]
    obtain ⟨τ, m⟩ := x
    simp only at h0 hN
    let p : ι × Fin N × Fin N := (τ, ⟨m, hN⟩, ⟨m - 1, by omega⟩)
    let S : Set (ι × Fin N × Fin N) := {z | z.2.2 < z.2.1}
    have hp : p ∈ S := by
      change (m : ℕ) - 1 < m
      omega
    have h := Set.ncard_diff_singleton_add_one hp
    refine Eq.trans (congrArg (· + 1) ?_) h
    refine Nat.card_congr (Equiv.subtypeEquivRight fun z => ?_)
    obtain ⟨σ, i, j⟩ := z
    change _ ↔ (j : ℕ) < i ∧ ¬ (σ, i, j) = p
    constructor
    · rintro ⟨⟨⟨σ', k⟩, hk⟩, rfl, h₁, h₂⟩
      simp only at h₁ h₂
      refine ⟨h₁.trans_le h₂, fun e => hk ?_⟩
      simp only [p, Prod.mk.injEq, Fin.ext_iff] at e ⊢
      exact ⟨e.1, by omega⟩
    · rintro ⟨h₁, h₂⟩
      by_cases e : (σ, j.succ) = (τ, m)
      · refine ⟨⟨(σ, i.castSucc), fun e' => h₂ ?_⟩, rfl, by simpa using h₁, by simp⟩
        simp only [p, Prod.mk.injEq, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc] at e e' ⊢
        exact ⟨e.1, by omega, by omega⟩
      · exact ⟨⟨(σ, j.succ), e⟩, rfl, by simp, by simpa using h₁⟩

end GlobalTheory.FlagZ.Count
