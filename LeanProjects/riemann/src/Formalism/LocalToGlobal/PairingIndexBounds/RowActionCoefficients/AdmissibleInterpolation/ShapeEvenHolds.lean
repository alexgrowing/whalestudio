import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.CoefProd
import Mathlib

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.L2.G.Model.TS

namespace ConjugatePartitionShape

section Heights

variable {n : ℕ} {ν : Fin n → ℕ}

theorem colH_ge (hν : Antitone ν) {k : ℕ} (t : Fin n) (h : k < ν t) : t.val + 1 ≤ colH ν k := by
  unfold colH
  rw [← Fin.card_Iic t]
  apply Finset.card_le_card
  intro s hs
  rw [Finset.mem_Iic] at hs
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, lt_of_lt_of_le h (hν hs)⟩

theorem colH_le_of (hν : Antitone ν) {k : ℕ} (t : Fin n) (h : ν t ≤ k) : colH ν k ≤ t.val := by
  unfold colH
  rw [← Fin.card_Iio t]
  apply Finset.card_le_card
  intro s hs
  rw [Finset.mem_filter] at hs
  rw [Finset.mem_Iio]
  by_contra hst
  push_neg at hst
  exact absurd (lt_of_lt_of_le hs.2 (hν hst)) (not_lt.mpr h)

theorem lt_colH_iff (hν : Antitone ν) (k : ℕ) (t : Fin n) : t.val < colH ν k ↔ k < ν t := by
  constructor
  · intro h
    by_contra h'
    push_neg at h'
    exact absurd (colH_le_of hν t h') (not_le.mpr h)
  · intro h
    exact Nat.lt_of_succ_le (colH_ge hν t h)

end Heights

theorem card_fin_lt (c m : ℕ) (hm : m ≤ c) : (Finset.univ.filter fun k : Fin c => k.val < m).card = m := by
  have e : (Finset.univ.filter fun k : Fin c => k.val < m).map Fin.valEmbedding = Finset.range m := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_range]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact hk
    · intro hx
      exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, e, Finset.card_range]

theorem kap_antitone {n : ℕ} {μ : Fin n → ℕ} (hμ : Antitone μ) (c : ℕ) : Antitone fun t : Fin n => c - μ t.rev := by
  intro s t hst
  exact Nat.sub_le_sub_left (hμ (Fin.rev_le_rev.mpr hst)) c

theorem colH_kap {n : ℕ} {μ : Fin n → ℕ} (c : ℕ) (hc : ∀ t, μ t ≤ c) (k : Fin c) :
    n - colH μ k.val = colH (fun t : Fin n => c - μ t.rev) (Fin.rev k).val := by
  simp only [colH]
  have e1 : (Finset.univ.filter fun t : Fin n => (Fin.rev k).val < c - μ t.rev).card =
      (Finset.univ.filter fun s : Fin n => ¬ k.val < μ s).card := by
    refine Finset.card_bij (fun t _ => t.rev) ?_ ?_ ?_
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_rev] at ht ⊢
      have := hc t.rev
      have := k.isLt
      omega
    · intro a _ b _ h
      exact Fin.rev_injective h
    · intro s hs
      refine ⟨s.rev, ?_, Fin.rev_rev s⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_rev, Fin.rev_rev] at hs ⊢
      have := hc s
      have := k.isLt
      omega
  have hsub : (Finset.univ.filter fun s : Fin n => k.val < μ s) ⊆ Finset.univ := Finset.subset_univ _
  have h2 := Finset.card_sdiff_add_card_eq_card hsub
  have h3 : (Finset.univ.filter fun s : Fin n => ¬ k.val < μ s) =
      Finset.univ \ (Finset.univ.filter fun s : Fin n => k.val < μ s) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
  rw [Finset.card_univ, Fintype.card_fin] at h2
  rw [h3] at e1
  omega

theorem card_ge_eq {n K K' : ℕ} (sz : Fin K → ℕ) (sz' : Fin K' → ℕ) (hsz : ∀ k, sz k ≤ n) (hsz' : ∀ k, sz' k ≤ n)
    (h : (shapeDeg sz : Fin n → ℕ) = shapeDeg sz') (l : ℕ) (hl : 0 < l) :
    (Finset.univ.filter fun k => l ≤ sz k).card = (Finset.univ.filter fun k => l ≤ sz' k).card := by
  by_cases hln : l ≤ n
  · have e := congrFun h ⟨l - 1, by omega⟩
    simp only [shapeDeg] at e
    have e1 : (Finset.univ.filter fun k => l ≤ sz k) = (Finset.univ.filter fun k => l - 1 < sz k) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor <;> intro <;> omega
    have e2 : (Finset.univ.filter fun k => l ≤ sz' k) = (Finset.univ.filter fun k => l - 1 < sz' k) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor <;> intro <;> omega
    rw [e1, e2]
    exact e
  · push_neg at hln
    have e1 : (Finset.univ.filter fun k => l ≤ sz k) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun k _ => by have := hsz k; omega
    have e2 : (Finset.univ.filter fun k => l ≤ sz' k) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun k _ => by have := hsz' k; omega
    rw [e1, e2, Finset.card_empty, Finset.card_empty]

theorem card_eq_sub {K : ℕ} (sz : Fin K → ℕ) (l : ℕ) :
    (Finset.univ.filter fun k => sz k = l).card =
      (Finset.univ.filter fun k => l ≤ sz k).card - (Finset.univ.filter fun k => l + 1 ≤ sz k).card := by
  have hsub : (Finset.univ.filter fun k => l + 1 ≤ sz k) ⊆ (Finset.univ.filter fun k => l ≤ sz k) := by
    intro k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have h2 := Finset.card_sdiff_add_card_eq_card hsub
  have h3 : (Finset.univ.filter fun k => sz k = l) =
      (Finset.univ.filter fun k => l ≤ sz k) \ (Finset.univ.filter fun k => l + 1 ≤ sz k) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    constructor <;> intro <;> omega
  rw [h3]
  omega

theorem card_eq_eq {n K K' : ℕ} (sz : Fin K → ℕ) (sz' : Fin K' → ℕ) (hsz : ∀ k, sz k ≤ n) (hsz' : ∀ k, sz' k ≤ n)
    (h : (shapeDeg sz : Fin n → ℕ) = shapeDeg sz') (l : ℕ) (hl : 0 < l) :
    Fintype.card {k' // sz' k' = l} = Fintype.card {k // sz k = l} := by
  rw [Fintype.card_subtype, Fintype.card_subtype, card_eq_sub, card_eq_sub,
    card_ge_eq sz sz' hsz hsz' h l hl, card_ge_eq sz sz' hsz hsz' h (l + 1) (Nat.succ_pos l)]

theorem initMinor_cast (B : Type) [CommRing B] {r n s s' : ℕ} (e : s = s') (J : Fin s → Fin r) (hs : s ≤ n)
    (hs' : s' ≤ n) : initMinor B (n := n) (fun j : Fin s' => J (Fin.cast e.symm j)) hs' = initMinor B J hs := by
  subst e
  rfl

theorem initMinor_zero (B : Type) [CommRing B] {r n : ℕ} (J : Fin 0 → Fin r) (hs : 0 ≤ n) :
    initMinor B (n := n) J hs = 1 := by
  rw [initMinor]
  exact Matrix.det_isEmpty

theorem initMinor_eq_one (B : Type) [CommRing B] {r n s : ℕ} (J : Fin s → Fin r) (hs : s ≤ n) (h0 : s = 0) :
    initMinor B (n := n) J hs = 1 := by
  subst h0
  exact initMinor_zero B J hs

end ConjugatePartitionShape

open ConjugatePartitionShape

theorem shape_even_holds : ShapeE := by
  intro n ν hν c hc
  funext t
  simp only [shapeDeg]
  rw [← card_fin_lt c (ν t) (hc t)]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact lt_colH_iff hν k.val t

theorem shape_odd_holds : ShapeO := by
  intro n μ hμ c hc
  funext t
  simp only [shapeDeg]
  rw [← card_fin_lt c (c - μ t.rev) (Nat.sub_le c _)]
  refine Finset.card_bij (fun k _ => Fin.rev k) ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    rw [colH_kap c (fun s => hc s) k] at hk
    exact (lt_colH_iff (kap_antitone hμ c) _ t).mp hk
  · intro a _ b _ h
    exact Fin.rev_injective h
  · intro k hk
    refine ⟨Fin.rev k, ?_, Fin.rev_rev k⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    rw [colH_kap c (fun s => hc s) (Fin.rev k), Fin.rev_rev]
    exact (lt_colH_iff (kap_antitone hμ c) _ t).mpr hk

theorem reorder_holds : Reorder := by
  intro B _ r n K K' sz sz' hsz hsz' h I
  classical
  have hE : ∀ l, 0 < l → Nonempty ({k' // sz' k' = l} ≃ {k // sz k = l}) := fun l hl =>
    ⟨Fintype.equivOfCardEq (card_eq_eq sz sz' hsz hsz' h l hl)⟩
  let e : ∀ l, 0 < l → ({k' // sz' k' = l} ≃ {k // sz k = l}) := fun l hl => Classical.choice (hE l hl)
  let I' : ∀ k', Fin (sz' k') → Fin r := fun k' =>
    if hk : 0 < sz' k' then
      fun j => I (e (sz' k') hk ⟨k', rfl⟩).1 (Fin.cast (e (sz' k') hk ⟨k', rfl⟩).2.symm j)
    else fun j => absurd j.2 (by omega)
  refine ⟨I', ?_⟩
  unfold bideterminant
  have hmaps : ∀ k ∈ (Finset.univ : Finset (Fin K)), sz k ∈ Finset.range (n + 1) :=
    fun k _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (hsz k))
  have hmaps' : ∀ k ∈ (Finset.univ : Finset (Fin K')), sz' k ∈ Finset.range (n + 1) :=
    fun k _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (hsz' k))
  rw [← Finset.prod_fiberwise_of_maps_to hmaps, ← Finset.prod_fiberwise_of_maps_to hmaps']
  refine Finset.prod_congr rfl fun l _ => ?_
  rcases Nat.eq_zero_or_pos l with hl | hl
  · subst hl
    rw [Finset.prod_eq_one, Finset.prod_eq_one]
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      exact initMinor_eq_one B _ _ hk
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      exact initMinor_eq_one B _ _ hk
  · rw [Finset.prod_subtype _ (p := fun k => sz k = l) (by simp),
      Finset.prod_subtype _ (p := fun k' => sz' k' = l) (by simp)]
    symm
    refine Fintype.prod_equiv (e l hl) _ _ fun x' => ?_
    obtain ⟨k', hk'⟩ := x'
    subst hk'
    have hI : I' k' = fun j => I (e (sz' k') hl ⟨k', rfl⟩).1 (Fin.cast (e (sz' k') hl ⟨k', rfl⟩).2.symm j) :=
      dif_pos hl
    simp only
    rw [hI]
    exact initMinor_cast B (e (sz' k') hl ⟨k', rfl⟩).2 _ _ _

end Formalism.L2.PairingIndexBounds.Ent
