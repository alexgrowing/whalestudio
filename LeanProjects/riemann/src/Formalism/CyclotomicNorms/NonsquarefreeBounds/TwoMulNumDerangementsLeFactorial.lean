import Formalism.CyclotomicNorms.DiscardKernel

open Finset

namespace Formalism.CyclotomicNorms.PermutationFixedPoints

theorem two_mul_numDerangements_le_factorial (m : ℕ) :
    2 * numDerangements (m + 1) ≤ (m + 1).factorial ∧
      2 * numDerangements (m + 2) ≤ (m + 2).factorial := by
  induction m with
  | zero => decide
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨h2, ?_⟩
    show 2 * numDerangements (m + 3) ≤ (m + 3).factorial
    have e : numDerangements (m + 3) =
        (m + 2) * (numDerangements (m + 1) + numDerangements (m + 2)) :=
      numDerangements_add_two (m + 1)
    have hf2 : (m + 2).factorial = (m + 2) * (m + 1).factorial := Nat.factorial_succ _
    have hf3 : (m + 3).factorial = (m + 3) * (m + 2).factorial := Nat.factorial_succ _
    rw [e, hf3, hf2]
    rw [hf2] at h2
    have k1 := Nat.mul_le_mul_left (m + 2) h1
    have k2 := Nat.mul_le_mul_left (m + 2) h2
    nlinarith

theorem two_mul_numDerangements_le (k : ℕ) (hk : 1 ≤ k) :
    2 * numDerangements k ≤ k.factorial := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  exact (two_mul_numDerangements_le_factorial m).1

theorem card_perm_with_fixed {α : Type*} [Fintype α] [DecidableEq α] (h : 1 ≤ Fintype.card α) :
    (Fintype.card α).factorial ≤
      2 * (univ.filter (fun p : Equiv.Perm α => ∃ x, p x = x)).card := by
  have hD := card_derangements_eq_numDerangements α
  have hsplit := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Equiv.Perm α)))
    (fun p => ∃ x, p x = x)
  have hneg : (univ.filter (fun p : Equiv.Perm α => ¬ ∃ x, p x = x)).card =
      Fintype.card (derangements α) := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun p => by
      simp only [not_exists]
      exact Iff.rfl))
  rw [card_univ, Fintype.card_perm, hneg, hD] at hsplit
  have := two_mul_numDerangements_le _ h
  omega

theorem map_eq_iff {α : Type*} [DecidableEq α] (σ : Equiv.Perm α) (S : Finset α) :
    S.map σ.toEmbedding = S ↔ ∀ x, σ x ∈ S ↔ x ∈ S := by
  rw [Finset.ext_iff]
  simp only [Finset.mem_map_equiv]
  constructor
  · intro h x
    simpa using (h (σ x)).symm
  · intro h b
    simpa using (h (σ.symm b)).symm

theorem inv_exchange {α : Type*} [DecidableEq α] (σ : Equiv.Perm α) (S : Finset α)
    (hS : ∀ z, σ z ∈ S ↔ z ∈ S) (x y : α) (hx : σ x = x) (hy : σ y = y) :
    ∀ z, σ z ∈ insert y (S.erase x) ↔ z ∈ insert y (S.erase x) := by
  intro z
  have e1 : σ z = y ↔ z = y :=
    ⟨fun h => σ.injective (h.trans hy.symm), fun h => h ▸ hy⟩
  have e2 : σ z = x ↔ z = x :=
    ⟨fun h => σ.injective (h.trans hx.symm), fun h => h ▸ hx⟩
  simp only [Finset.mem_insert, Finset.mem_erase, ne_eq, e1, e2, hS]

def numInv (N a : ℕ) (σ : Equiv.Perm (Fin N)) : ℕ :=
  (((univ : Finset (Fin N)).powersetCard a).filter (fun S => ∀ x, σ x ∈ S ↔ x ∈ S)).card

theorem sum_numInv (N a : ℕ) :
    ∑ σ : Equiv.Perm (Fin N), numInv N a σ =
      ∑ S ∈ (univ : Finset (Fin N)).powersetCard a,
        (univ.filter (fun σ : Equiv.Perm (Fin N) => ∀ x, σ x ∈ S ↔ x ∈ S)).card := by
  simp only [numInv, Finset.card_filter]
  exact Finset.sum_comm

theorem sum_numInv_two (N a : ℕ) :
    ∑ σ : Equiv.Perm (Fin N), (if 2 ≤ numInv N a σ then numInv N a σ else 0) =
      ∑ S ∈ (univ : Finset (Fin N)).powersetCard a,
        (univ.filter (fun σ : Equiv.Perm (Fin N) =>
          (∀ x, σ x ∈ S ↔ x ∈ S) ∧ 2 ≤ numInv N a σ)).card := by
  calc ∑ σ : Equiv.Perm (Fin N), (if 2 ≤ numInv N a σ then numInv N a σ else 0)
      = ∑ σ : Equiv.Perm (Fin N), ∑ S ∈ (univ : Finset (Fin N)).powersetCard a,
          (if ((∀ x, σ x ∈ S ↔ x ∈ S) ∧ 2 ≤ numInv N a σ) then 1 else 0) := by
        refine Finset.sum_congr rfl (fun σ _ => ?_)
        by_cases h : 2 ≤ numInv N a σ
        · simp only [h, if_true, and_true]
          rw [numInv, Finset.card_filter]
        · simp [h]
    _ = _ := by
        rw [Finset.sum_comm]
        simp only [Finset.card_filter]

theorem card_stab_le (N : ℕ) (S : Finset (Fin N)) :
    (univ.filter (fun σ : Equiv.Perm (Fin N) => ∀ x, σ x ∈ S ↔ x ∈ S)).card ≤
      S.card.factorial * (N - S.card).factorial := by
  have hsub : univ.filter (fun σ : Equiv.Perm (Fin N) => ∀ x, σ x ∈ S ↔ x ∈ S) ⊆
      (univ : Finset (Equiv.Perm {x // x ∈ S} × Equiv.Perm {x // x ∉ S})).image
        (Equiv.Perm.subtypeCongrHom (fun x => x ∈ S)) := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨(σ.subtypePerm (p := fun x => x ∈ S) (fun x => hσ x),
      σ.subtypePerm (p := fun x => x ∉ S) (fun x => not_congr (hσ x))), ?_⟩
    ext z
    rw [Equiv.Perm.subtypeCongrHom_apply]
    by_cases hz : z ∈ S
    · rw [Equiv.Perm.subtypeCongr.left_apply _ _ hz]
      rfl
    · rw [Equiv.Perm.subtypeCongr.right_apply _ _ hz]
      rfl
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_image_le
    _ = _ := by
      rw [Finset.card_univ, Fintype.card_prod, Fintype.card_perm, Fintype.card_perm,
        Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin]

theorem card_good_ge (N a : ℕ) (ha : 0 < a) (haN : a < N) (S : Finset (Fin N))
    (hS : S.card = a) :
    a.factorial * (N - a).factorial ≤
      4 * (univ.filter (fun σ : Equiv.Perm (Fin N) =>
        (∀ x, σ x ∈ S ↔ x ∈ S) ∧ 2 ≤ numInv N a σ)).card := by
  set P := univ.filter (fun p : Equiv.Perm {x // x ∈ S} => ∃ x, p x = x) with hPdef
  set Q := univ.filter (fun q : Equiv.Perm {x // x ∉ S} => ∃ y, q y = y) with hQdef
  have hcS : Fintype.card {x // x ∈ S} = a := by rw [Fintype.card_coe, hS]
  have hcT : Fintype.card {x // x ∉ S} = N - a := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin, hS]
  have hP := card_perm_with_fixed (α := {x // x ∈ S}) (by omega)
  have hQ := card_perm_with_fixed (α := {x // x ∉ S}) (by omega)
  rw [hcS] at hP
  rw [hcT] at hQ
  have hsub : (P ×ˢ Q).image (Equiv.Perm.subtypeCongrHom (fun x => x ∈ S)) ⊆
      univ.filter (fun σ : Equiv.Perm (Fin N) =>
        (∀ x, σ x ∈ S ↔ x ∈ S) ∧ 2 ≤ numInv N a σ) := by
    intro σ hσ
    simp only [Finset.mem_image, Finset.mem_product, hPdef, hQdef, Finset.mem_filter,
      Finset.mem_univ, true_and] at hσ
    obtain ⟨⟨p, q⟩, ⟨⟨x, hx⟩, ⟨y, hy⟩⟩, rfl⟩ := hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hinv : ∀ z, (Equiv.Perm.subtypeCongrHom (fun x => x ∈ S) (p, q)) z ∈ S ↔ z ∈ S := by
      intro z
      rw [Equiv.Perm.subtypeCongrHom_apply]
      by_cases hz : z ∈ S
      · rw [Equiv.Perm.subtypeCongr.left_apply _ _ hz]
        simp [hz, (p ⟨z, hz⟩).2]
      · rw [Equiv.Perm.subtypeCongr.right_apply _ _ hz]
        simp [hz, (q ⟨z, hz⟩).2]
    have hxσ : (Equiv.Perm.subtypeCongrHom (fun x => x ∈ S) (p, q)) (x : Fin N) = x := by
      rw [Equiv.Perm.subtypeCongrHom_apply, Equiv.Perm.subtypeCongr.left_apply _ _ x.2]
      simp [hx]
    have hyσ : (Equiv.Perm.subtypeCongrHom (fun x => x ∈ S) (p, q)) (y : Fin N) = y := by
      rw [Equiv.Perm.subtypeCongrHom_apply, Equiv.Perm.subtypeCongr.right_apply _ _ y.2]
      simp [hy]
    refine ⟨hinv, ?_⟩
    have hy' : (y : Fin N) ∉ S.erase x := fun h => y.2 (Finset.mem_of_mem_erase h)
    refine Finset.one_lt_card.2 ⟨S, ?_, insert (y : Fin N) (S.erase x), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_powersetCard]
      exact ⟨⟨Finset.subset_univ _, hS⟩, hinv⟩
    · simp only [Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨Finset.subset_univ _, ?_⟩, inv_exchange _ S hinv x y hxσ hyσ⟩
      rw [Finset.card_insert_of_notMem hy', Finset.card_erase_of_mem x.2, hS]
      omega
    · intro h
      have hm : (y : Fin N) ∈ insert (y : Fin N) (S.erase x) := Finset.mem_insert_self _ _
      rw [← h] at hm
      exact y.2 hm
  have hcard : ((P ×ˢ Q).image (Equiv.Perm.subtypeCongrHom (fun x => x ∈ S))).card =
      P.card * Q.card := by
    rw [Finset.card_image_of_injective _ (Equiv.Perm.subtypeCongrHom_injective _),
      Finset.card_product]
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  calc a.factorial * (N - a).factorial ≤ (2 * P.card) * (2 * Q.card) := Nat.mul_le_mul hP hQ
    _ = 4 * (P.card * Q.card) := by ring
    _ ≤ _ := Nat.mul_le_mul_left 4 hle

theorem main : PermFixedSet := by
  intro N a ha haN
  have hpt : ∀ σ : Equiv.Perm (Fin N),
      8 * (if (∃ S : Finset (Fin N), S.card = a ∧ S.map σ.toEmbedding = S) then 1 else 0) +
        4 * (if 2 ≤ numInv N a σ then numInv N a σ else 0) ≤ 8 * numInv N a σ := by
    intro σ
    by_cases hA : ∃ S : Finset (Fin N), S.card = a ∧ S.map σ.toEmbedding = S
    · have h1 : 1 ≤ numInv N a σ := by
        obtain ⟨S, hSc, hSm⟩ := hA
        unfold numInv
        apply Finset.card_pos.2
        refine ⟨S, ?_⟩
        simp only [Finset.mem_filter, Finset.mem_powersetCard]
        exact ⟨⟨Finset.subset_univ _, hSc⟩, (map_eq_iff σ S).1 hSm⟩
      rw [if_pos hA]
      split_ifs <;> omega
    · rw [if_neg hA]
      split_ifs <;> omega
  have hsum := Finset.sum_le_sum (s := (univ : Finset (Equiv.Perm (Fin N)))) (fun σ _ => hpt σ)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.card_filter] at hsum
  have hconst : ∑ S ∈ (univ : Finset (Fin N)).powersetCard a,
      a.factorial * (N - a).factorial = N.factorial := by
    rw [Finset.sum_const, smul_eq_mul, Finset.card_powersetCard, Finset.card_univ,
      Fintype.card_fin, ← mul_assoc, Nat.choose_mul_factorial_mul_factorial haN.le]
  have hX : ∑ σ : Equiv.Perm (Fin N), numInv N a σ ≤ N.factorial := by
    rw [sum_numInv, ← hconst]
    refine Finset.sum_le_sum (fun S hS => ?_)
    rw [Finset.mem_powersetCard] at hS
    have := card_stab_le N S
    rwa [hS.2] at this
  have hX2 : N.factorial ≤
      4 * ∑ σ : Equiv.Perm (Fin N), (if 2 ≤ numInv N a σ then numInv N a σ else 0) := by
    rw [sum_numInv_two, Finset.mul_sum, ← hconst]
    refine Finset.sum_le_sum (fun S hS => ?_)
    rw [Finset.mem_powersetCard] at hS
    exact card_good_ge N a ha haN S hS.2
  omega

end Formalism.CyclotomicNorms.PermutationFixedPoints
