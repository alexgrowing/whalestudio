import Mathlib

namespace GlobalTheory

theorem card_record_indices_le_of_chain_bound {α : Type} [Preorder α] (Q : α → Prop) (L : ℕ)
    (h : ∀ (r : ℕ) (N : Fin r → α), StrictMono N → (∀ i, Q (N i)) → r ≤ L)
    {r : ℕ} (a : Fin r → α) (ha : ∀ i, Q (a i)) (T : Finset (Fin r))
    (hT : ∀ j ∈ T, ∀ i < j, a i < a j) : T.card ≤ L := by
  refine h T.card (fun k => a (T.orderEmbOfFin rfl k)) ?_ (fun k => ha _)
  intro k k' hk
  exact hT _ (T.orderEmbOfFin_mem rfl k') _ ((T.orderEmbOfFin rfl).strictMono hk)

theorem modular_chain_bound_add {α : Type} [Lattice α] [IsModularLattice α] (C : α)
    (Q Q1 Q2 : α → Prop) (L1 L2 : ℕ)
    (hQ1 : ∀ x, Q x → Q1 (x ⊓ C)) (hQ2 : ∀ x, Q x → Q2 (x ⊔ C))
    (h1 : ∀ (r : ℕ) (N : Fin r → α), StrictMono N → (∀ i, Q1 (N i)) → r ≤ L1)
    (h2 : ∀ (r : ℕ) (N : Fin r → α), StrictMono N → (∀ i, Q2 (N i)) → r ≤ L2)
    (r : ℕ) (N : Fin r → α) (hN : StrictMono N) (hQ : ∀ i, Q (N i)) : r ≤ L1 + L2 := by
  classical
  let Ta : Finset (Fin r) := Finset.univ.filter fun j => ∀ i < j, N i ⊓ C < N j ⊓ C
  let Tb : Finset (Fin r) := Finset.univ.filter fun j => ∀ i < j, N i ⊔ C < N j ⊔ C
  have hA : Ta.card ≤ L1 :=
    card_record_indices_le_of_chain_bound Q1 L1 h1 (fun i => N i ⊓ C) (fun i => hQ1 _ (hQ i)) Ta
      (fun j hj => (Finset.mem_filter.1 hj).2)
  have hB : Tb.card ≤ L2 :=
    card_record_indices_le_of_chain_bound Q2 L2 h2 (fun i => N i ⊔ C) (fun i => hQ2 _ (hQ i)) Tb
      (fun j hj => (Finset.mem_filter.1 hj).2)
  have hU : (Finset.univ : Finset (Fin r)) ⊆ Ta ∪ Tb := by
    intro j _
    by_contra hj
    simp only [Ta, Tb, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, not_or,
      not_forall] at hj
    obtain ⟨⟨i, hi, hia⟩, ⟨i', hi', hib⟩⟩ := hj
    have hk : max i i' < j := max_lt hi hi'
    have ea : N i ⊓ C = N j ⊓ C :=
      eq_of_le_of_not_lt (inf_le_inf_right C (hN hi).le) hia
    have eb : N i' ⊔ C = N j ⊔ C :=
      eq_of_le_of_not_lt (sup_le_sup_right (hN hi').le C) hib
    have e : N (max i i') = N j :=
      eq_of_le_of_inf_le_of_sup_le (hN hk).le
        (ea ▸ inf_le_inf_right C (hN.monotone (le_max_left i i')))
        (eb ▸ sup_le_sup_right (hN.monotone (le_max_right i i')) C)
    exact (hN hk).ne e
  have := (Finset.card_le_card hU).trans (Finset.card_union_le Ta Tb)
  rw [Finset.card_univ, Fintype.card_fin] at this
  omega

end GlobalTheory
