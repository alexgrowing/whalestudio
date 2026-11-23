import Formalism.PadicSubsetSums.CentralIdempotents.GaloisIrreducibility

open Finset

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem two_numDerangements_le (n : ℕ) (hn : 1 ≤ n) : 2 * numDerangements n ≤ n.factorial := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, hn with
    | 1, _ => simp [numDerangements_one]
    | 2, _ => simp [numDerangements_add_two, numDerangements_zero, numDerangements_one, Nat.factorial]
    | k + 3, _ =>
      have h1 := ih (k + 1) (by omega) (by omega)
      have h2 := ih (k + 2) (by omega) (by omega)
      show 2 * numDerangements (k + 1 + 2) ≤ (k + 1 + 2).factorial
      rw [numDerangements_add_two, Nat.factorial_succ (k + 1 + 1)]
      rw [show k + 1 + 1 = k + 2 from rfl, Nat.factorial_succ (k + 1)] at *
      nlinarith [h1, h2]

theorem card_fixed_ge (β : Type) [Fintype β] [DecidableEq β] (hβ : 1 ≤ Fintype.card β) :
    (Fintype.card β).factorial ≤
      2 * ((univ : Finset (Equiv.Perm β)).filter (fun s => ∃ x, s x = x)).card := by
  have hd := card_derangements_eq_numDerangements β
  have h2 := two_numDerangements_le _ hβ
  have hsplit : ((univ : Finset (Equiv.Perm β)).filter (fun s => ∃ x, s x = x)).card +
      ((univ : Finset (Equiv.Perm β)).filter (fun s => ¬ ∃ x, s x = x)).card =
      (Fintype.card β).factorial := by
    rw [← Fintype.card_perm, ← Finset.card_univ]
    first
    | exact Finset.card_filter_add_card_filter_not _
    | exact Finset.filter_card_add_filter_neg_card_eq_card _
    | exact Finset.card_filter_add_card_filter_neg _
  have hneg : ((univ : Finset (Equiv.Perm β)).filter (fun s => ¬ ∃ x, s x = x)).card =
      Fintype.card (derangements β) := by
    rw [Fintype.card_subtype]
    congr 1
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists]
    exact Iff.rfl
  omega

section

variable {N : ℕ}

theorem stab_iff (A : Finset (Fin N)) (σ : Equiv.Perm (Fin N)) (h : ∀ x ∈ A, σ x ∈ A) (x : Fin N) :
    σ x ∈ A ↔ x ∈ A := by
  constructor
  · intro hx
    by_contra hxA
    have hsub : A.image σ ⊆ A := fun y hy => by
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      exact h z hz
    have hcard : (A.image σ).card = A.card := Finset.card_image_of_injective A σ.injective
    have heq := Finset.eq_of_subset_of_card_le hsub hcard.ge
    rw [← heq] at hx
    obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hx
    exact hxA (σ.injective hzx ▸ hz)
  · exact h x

theorem card_stab_le (A : Finset (Fin N)) :
    ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => ∀ x ∈ A, σ x ∈ A)).card ≤
      A.card.factorial * (N - A.card).factorial := by
  have key : Fintype.card {σ : Equiv.Perm (Fin N) // ∀ x ∈ A, σ x ∈ A} ≤
      Fintype.card (Equiv.Perm {x // x ∈ A} × Equiv.Perm {x // x ∉ A}) := by
    refine Fintype.card_le_of_injective
      (fun σ => (σ.1.subtypePerm (fun x => stab_iff A σ.1 σ.2 x),
        σ.1.subtypePerm (fun x => not_congr (stab_iff A σ.1 σ.2 x)))) ?_
    rintro ⟨σ, hσ⟩ ⟨τ, hτ⟩ he
    simp only [Prod.mk.injEq] at he
    apply Subtype.ext
    ext x
    by_cases hx : x ∈ A
    · have := congrArg (fun e => (e ⟨x, hx⟩ : Fin N)) he.1
      exact congrArg Fin.val (by simpa using this)
    · have := congrArg (fun e => (e ⟨x, hx⟩ : Fin N)) he.2
      exact congrArg Fin.val (by simpa using this)
  rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_perm, Fintype.card_coe,
    Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe] at key
  calc _ = Fintype.card {σ : Equiv.Perm (Fin N) // ∀ x ∈ A, σ x ∈ A} := (Fintype.card_subtype _).symm
    _ ≤ _ := key

theorem card_good_ge (A : Finset (Fin N)) (h1 : 1 ≤ A.card) (h2 : 1 ≤ N - A.card) :
    A.card.factorial * (N - A.card).factorial ≤
      4 * ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => (∀ x ∈ A, σ x ∈ A) ∧
        (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y)).card := by
  set P : Finset (Equiv.Perm {x // x ∈ A}) := univ.filter (fun s => ∃ x, s x = x) with hP
  set Q : Finset (Equiv.Perm {x // x ∉ A}) := univ.filter (fun s => ∃ x, s x = x) with hQ
  have hP1 : A.card.factorial ≤ 2 * P.card := by
    have := card_fixed_ge {x // x ∈ A} (by rw [Fintype.card_coe]; exact h1)
    rwa [Fintype.card_coe] at this
  have hc : Fintype.card {x // x ∉ A} = N - A.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
  have hQ1 : (N - A.card).factorial ≤ 2 * Q.card := by
    have := card_fixed_ge {x // x ∉ A} (by rw [hc]; exact h2)
    rwa [hc] at this
  have hinj : (P ×ˢ Q).card ≤ ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => (∀ x ∈ A, σ x ∈ A) ∧
      (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y)).card := by
    refine Finset.card_le_card_of_injOn (fun q => Equiv.Perm.subtypeCongr q.1 q.2) ?_ ?_
    · rintro ⟨α, β⟩ hq
      simp only [Finset.mem_coe, Finset.mem_product, hP, hQ, Finset.mem_filter, Finset.mem_univ,
        true_and] at hq
      obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun z hz => ?_, ⟨x.1, x.2, ?_⟩, ⟨y.1, y.2, ?_⟩⟩
      · simp [Equiv.Perm.subtypeCongr.left_apply, hz]
      · simp [Equiv.Perm.subtypeCongr.left_apply, x.2, hx]
      · simp [Equiv.Perm.subtypeCongr.right_apply, y.2, hy]
    · rintro ⟨α, β⟩ _ ⟨α', β'⟩ _ he
      simp only at he
      have hA : α = α' := by
        ext ⟨z, hz⟩
        have := congrArg (fun e : Equiv.Perm (Fin N) => e z) he
        have h' : α ⟨z, hz⟩ = α' ⟨z, hz⟩ := by
          simpa [Equiv.Perm.subtypeCongr.left_apply, hz] using this
        rw [h']
      have hB : β = β' := by
        ext ⟨z, hz⟩
        have := congrArg (fun e : Equiv.Perm (Fin N) => e z) he
        have h' : (β ⟨z, hz⟩ : Fin N) = β' ⟨z, hz⟩ := by
          simpa [Equiv.Perm.subtypeCongr.right_apply, hz] using this
        rw [h']
      rw [hA, hB]
  rw [Finset.card_product] at hinj
  calc A.card.factorial * (N - A.card).factorial ≤ (2 * P.card) * (2 * Q.card) :=
        Nat.mul_le_mul hP1 hQ1
    _ = 4 * (P.card * Q.card) := by ring
    _ ≤ _ := Nat.mul_le_mul_left 4 hinj

end

theorem prodMaxInvLeSq : LemmaP := by
  intro N a ha haN
  have key : ∀ σ : Equiv.Perm (Fin N),
      2 * (if (∃ A : Finset (Fin N), A.card = a ∧ ∀ x ∈ A, σ x ∈ A) then 1 else 0) + (((univ : Finset (Fin N)).powersetCard a).filter (fun A => (∀ x ∈ A, σ x ∈ A) ∧ (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y)).card ≤ 2 * (((univ : Finset (Fin N)).powersetCard a).filter (fun A => ∀ x ∈ A, σ x ∈ A)).card := by
    intro σ
    have hsub : ((univ : Finset (Fin N)).powersetCard a).filter (fun A => (∀ x ∈ A, σ x ∈ A) ∧ (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y) ⊆ ((univ : Finset (Fin N)).powersetCard a).filter (fun A => ∀ x ∈ A, σ x ∈ A) := by
      intro A hA
      simp only [Finset.mem_filter] at hA ⊢
      exact ⟨hA.1, hA.2.1⟩
    have hle := Finset.card_le_card hsub
    split_ifs with hX
    · obtain ⟨A0, hA0c, hA0⟩ := hX
      have h1 : 1 ≤ (((univ : Finset (Fin N)).powersetCard a).filter (fun A => ∀ x ∈ A, σ x ∈ A)).card := by
        apply Finset.card_pos.mpr
        exact ⟨A0, Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hA0c⟩, hA0⟩⟩
      by_cases hg : (((univ : Finset (Fin N)).powersetCard a).filter (fun A => (∀ x ∈ A, σ x ∈ A) ∧ (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y)).card = 0
      · omega
      · obtain ⟨A, hA⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hg)
        simp only [Finset.mem_filter, Finset.mem_powersetCard] at hA
        obtain ⟨⟨-, hAc⟩, hinv, ⟨x, hxA, hx⟩, ⟨y, hyA, hy⟩⟩ := hA
        have hyE : y ∉ A.erase x := fun h => hyA (Finset.mem_of_mem_erase h)
        have h2 : 1 < (((univ : Finset (Fin N)).powersetCard a).filter (fun A => ∀ x ∈ A, σ x ∈ A)).card := by
          rw [Finset.one_lt_card]
          refine ⟨A, ?_, insert y (A.erase x), ?_, ?_⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hAc⟩, hinv⟩
          · simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
            refine ⟨?_, ?_⟩
            · rw [Finset.card_insert_of_notMem hyE, Finset.card_erase_of_mem hxA]
              have : 1 ≤ A.card := Finset.card_pos.mpr ⟨x, hxA⟩
              omega
            · intro z hz
              rcases Finset.mem_insert.mp hz with rfl | hz
              · rw [hy]
                exact Finset.mem_insert_self _ _
              · have hzA := Finset.mem_of_mem_erase hz
                have hzx := Finset.ne_of_mem_erase hz
                apply Finset.mem_insert_of_mem
                refine Finset.mem_erase.mpr ⟨?_, hinv z hzA⟩
                intro h
                apply hzx
                apply σ.injective
                rw [h, hx]
          · intro h
            apply hyA
            rw [h]
            exact Finset.mem_insert_self _ _
        omega
    · omega
  have hsum := Finset.sum_le_sum (fun σ (_ : σ ∈ (univ : Finset (Equiv.Perm (Fin N)))) => key σ)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hX : ∑ σ : Equiv.Perm (Fin N), (if (∃ A : Finset (Fin N), A.card = a ∧ ∀ x ∈ A, σ x ∈ A) then 1 else 0) =
      ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => (∃ A : Finset (Fin N), A.card = a ∧ ∀ x ∈ A, σ x ∈ A))).card :=
    (Finset.card_filter _ _).symm
  have hs1 : ∑ σ : Equiv.Perm (Fin N), (((univ : Finset (Fin N)).powersetCard a).filter (fun A => ∀ x ∈ A, σ x ∈ A)).card =
      ∑ A ∈ ((univ : Finset (Fin N)).powersetCard a), ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => ∀ x ∈ A, σ x ∈ A)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hs2 : ∑ σ : Equiv.Perm (Fin N), (((univ : Finset (Fin N)).powersetCard a).filter (fun A => (∀ x ∈ A, σ x ∈ A) ∧ (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y)).card =
      ∑ A ∈ ((univ : Finset (Fin N)).powersetCard a), ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => (∀ x ∈ A, σ x ∈ A) ∧ (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hfac : ∑ _A ∈ ((univ : Finset (Fin N)).powersetCard a), a.factorial * (N - a).factorial = N.factorial := by
    rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      ← mul_assoc]
    exact Nat.choose_mul_factorial_mul_factorial haN.le
  have hinv : ∑ A ∈ ((univ : Finset (Fin N)).powersetCard a), ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => ∀ x ∈ A, σ x ∈ A)).card ≤ N.factorial := by
    rw [← hfac]
    apply Finset.sum_le_sum
    intro A hA
    rw [Finset.mem_powersetCard] at hA
    have := card_stab_le A
    rwa [hA.2] at this
  have hgood : N.factorial ≤ 4 * ∑ A ∈ ((univ : Finset (Fin N)).powersetCard a), ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => (∀ x ∈ A, σ x ∈ A) ∧ (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y)).card := by
    rw [← hfac, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro A hA
    rw [Finset.mem_powersetCard] at hA
    have := card_good_ge A (by omega) (by omega)
    rwa [hA.2] at this
  rw [hX, hs1, hs2] at hsum
  omega

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
