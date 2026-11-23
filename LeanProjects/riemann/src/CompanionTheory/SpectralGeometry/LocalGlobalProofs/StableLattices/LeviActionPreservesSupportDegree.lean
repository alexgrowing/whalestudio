import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy

noncomputable section

namespace GlobalTheory.CompanionTheory.RgCOBlock.LeviSupp

open Finset
open CompanionTheory.D.LK (Pos Cn ann cre lift sg)
open CompanionTheory.RgExh.U

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem cre_ann_ne (i k : Pos n) (x : Cn n V) (A : Finset (Pos n))
    (h : (cre k * ann i : Module.End ℂ (Cn n V)) x A ≠ 0) :
    k ∈ A ∧ i ∉ A.erase k ∧ x (insert i (A.erase k)) ≠ 0 := by
  change (if k ∈ A then sg k A • (if i ∈ A.erase k then 0 else
    sg i (A.erase k) • x (insert i (A.erase k))) else 0) ≠ 0 at h
  by_cases hk : k ∈ A
  · by_cases hi : i ∈ A.erase k
    · rw [if_pos hk, if_pos hi, smul_zero] at h
      exact absurd rfl h
    · refine ⟨hk, hi, fun hx => ?_⟩
      rw [if_pos hk, if_neg hi, hx, smul_zero, smul_zero] at h
      exact h rfl
  · rw [if_neg hk] at h
    exact absurd rfl h

theorem lF_ne (E : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) (x : Cn n V) (A : Finset (Pos n))
    (h : lF E p q x A ≠ 0) :
    x A ≠ 0 ∨ ∃ i k : Pos n, adC p q i k ≠ 0 ∧ (cre k * ann i : Module.End ℂ (Cn n V)) x A ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h0, hall⟩ := hcon
  apply h
  change ((lift n (E p q) + adL p q : Module.End ℂ (Cn n V)) x) A = 0
  rw [LinearMap.add_apply, Pi.add_apply, CompanionTheory.D.LK.lift_apply, h0, map_zero, zero_add]
  unfold adL
  rw [LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [LinearMap.smul_apply, Pi.smul_apply]
  by_cases hc : adC p q i k = 0
  · rw [hc, zero_smul]
  · rw [hall i k hc, smul_zero]

theorem inU_of_adC {lev : Fin n → ℕ} {p q : Fin n} (hpq : lev p = lev q) {i k : Pos n}
    (h : adC p q i k ≠ 0) (hi : inU lev i) : inU lev k := by
  unfold adC at h
  unfold inU at hi ⊢
  by_cases h1 : q = (i : Fin n × Fin n).1 ∧ (k : Fin n × Fin n) = (p, (i : Fin n × Fin n).2)
  · rw [h1.2]
    show lev p < lev (i : Fin n × Fin n).2
    rw [hpq, h1.1]
    exact hi
  · by_cases h2 : (i : Fin n × Fin n).2 = p ∧ (k : Fin n × Fin n) = ((i : Fin n × Fin n).1, q)
    · rw [h2.2]
      show lev (i : Fin n × Fin n).1 < lev q
      rw [← hpq, ← h2.1]
      exact hi
    · rw [if_neg h1, if_neg h2, sub_zero] at h
      exact absurd rfl h

theorem lF_suppIn_deg (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (_hlev : Monotone lev) (x : Cn n V)
    (hx : SuppIn (inU lev) x) (p q : Fin n) (hpq : lev p = lev q) :
    SuppIn (inU lev) (lF E p q x) ∧ ∀ j, Deg j x → Deg j (lF E p q x) := by
  unfold SuppIn at hx ⊢
  unfold Deg
  constructor
  · intro A hA l hl
    rcases lF_ne E p q x A hA with h0 | ⟨i, k, hc, hne⟩
    · exact hx A h0 l hl
    · obtain ⟨hk, hi, hx'⟩ := cre_ann_ne i k x A hne
      have hsupp := hx _ hx'
      by_cases hlk : l = k
      · subst hlk
        exact inU_of_adC hpq hc (hsupp i (Finset.mem_insert_self _ _))
      · exact hsupp l (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hlk, hl⟩))
  · intro j hj A hA
    rcases lF_ne E p q x A hA with h0 | ⟨i, k, hc, hne⟩
    · exact hj A h0
    · obtain ⟨hk, hi, hx'⟩ := cre_ann_ne i k x A hne
      have hcard := hj _ hx'
      rw [Finset.card_insert_of_notMem hi, Finset.card_erase_of_mem hk] at hcard
      have hpos : 0 < A.card := Finset.card_pos.2 ⟨k, hk⟩
      omega

end GlobalTheory.CompanionTheory.RgCOBlock.LeviSupp
