import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertDensity.FinrankValPerp

open Finset Module

noncomputable section

namespace DensInertW

theorem valZ_succ (q d : ℕ) :
    valZ q (d + 1) + q * valZ q d = ((q : ℤ) + 1) * ((q : ℤ) ^ 2) ^ d := by
  unfold valZ
  cases d with
  | zero =>
    norm_num
    ring
  | succ d =>
    rw [show 2 * (d + 1 + 1) - 1 = 2 * d + 3 by omega, show d + 1 + 1 - 1 = d + 1 by omega,
      show 2 * (d + 1) - 1 = 2 * d + 1 by omega, show d + 1 - 1 = d by omega]
    ring

theorem valN_succ (q d : ℕ) :
    valN q (d + 1) + q * valN q d = ((q : ℤ) + 1) * ((q : ℤ) ^ 2) ^ d := by
  unfold valN
  cases d with
  | zero => norm_num
  | succ d =>
    rw [show d + 1 + 1 - 1 = d + 1 by omega, show d + 1 - 1 = d by omega]
    ring

section
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L] {n : ℕ}
  {M : Matrix (Fin n) (Fin n) L}

theorem val_recursion (h2 : finrank K L = 2) (hM : IsHerm (Fintype.card K) M)
    {W : Submodule L (Fin n → L)} {e : Fin n → L} (he : e ∈ W)
    (hb : hf (Fintype.card K) M e e ≠ 0) (a : L) (ha : a ^ Fintype.card K = a) :
    ((({v | v ∈ W ∧ hf (Fintype.card K) M v v = a} : Set (Fin n → L)).ncard : ℕ) : ℤ) +
      (Fintype.card K : ℤ) *
        ((({v | v ∈ valPerp (Fintype.card K) M W e ∧ hf (Fintype.card K) M v v = a} :
          Set (Fin n → L)).ncard : ℕ) : ℤ) =
      ((Fintype.card K : ℤ) + 1) *
        (Fintype.card L : ℤ) ^ finrank L (valPerp (Fintype.card K) M W e) := by
  classical
  have hbq : (hf (Fintype.card K) M e e) ^ Fintype.card K = (hf (Fintype.card K) M e e) := val_fixed h2 hM e
  let F : L × (valPerp (Fintype.card K) M W e) → (Fin n → L) := fun p => p.1 • e + (p.2 : Fin n → L)
  have hFe : ∀ p : L × (valPerp (Fintype.card K) M W e), hf (Fintype.card K) M (F p) e = p.1 * (hf (Fintype.card K) M e e) := by
    intro p
    have hw := (mem_valPerp.1 p.2.2).2
    show hf (Fintype.card K) M (p.1 • e + (p.2 : Fin n → L)) e = p.1 * (hf (Fintype.card K) M e e)
    rw [val_add_left, val_smul_left, hw, add_zero]
  have hFv : ∀ p : L × (valPerp (Fintype.card K) M W e), hf (Fintype.card K) M (F p) (F p) =
      p.1 ^ (Fintype.card K + 1) * (hf (Fintype.card K) M e e) + hf (Fintype.card K) M (p.2 : Fin n → L) p.2 := by
    intro p
    exact val_expand h2 hM e p.2 (mem_valPerp.1 p.2.2).2 p.1
  have hFinj : Function.Injective F := by
    rintro ⟨l, w⟩ ⟨l', w'⟩ h
    have h1 : l = l' := by
      have h3 := congrArg (fun v => hf (Fintype.card K) M v e) h
      have h4 : l * (hf (Fintype.card K) M e e) = l' * (hf (Fintype.card K) M e e) := by
        have e1 := hFe (l, w)
        have e2 := hFe (l', w')
        rw [← e1, ← e2]
        exact h3
      exact mul_right_cancel₀ hb h4
    subst h1
    have h5 : (w : Fin n → L) = w' := by
      have h6 : l • e + (w : Fin n → L) = l • e + (w' : Fin n → L) := h
      exact add_left_cancel h6
    exact Prod.ext rfl (Subtype.ext h5)
  have hS : {v | v ∈ W ∧ hf (Fintype.card K) M v v = a} =
      F '' {p | p.1 ^ (Fintype.card K + 1) * (hf (Fintype.card K) M e e) + hf (Fintype.card K) M (p.2 : Fin n → L) p.2 = a} := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hvW, hva⟩
      obtain ⟨l, hl⟩ : ∃ l : L, l = hf (Fintype.card K) M v e / (hf (Fintype.card K) M e e) := ⟨_, rfl⟩
      have hwP : v - l • e ∈ (valPerp (Fintype.card K) M W e) := by
        refine mem_valPerp.2 ⟨W.sub_mem hvW (W.smul_mem l he), ?_⟩
        rw [val_sub_left, val_smul_left, hl, div_mul_cancel₀ _ hb, sub_self]
      have hFl : F (l, ⟨v - l • e, hwP⟩) = v := by
        show l • e + (v - l • e) = v
        abel
      refine ⟨(l, ⟨v - l • e, hwP⟩), ?_, hFl⟩
      have h3 := hFv (l, ⟨v - l • e, hwP⟩)
      rw [hFl, hva] at h3
      exact h3.symm
    · rintro ⟨⟨l, w⟩, hp, rfl⟩
      refine ⟨?_, ?_⟩
      · exact W.add_mem (W.smul_mem l he) (mem_valPerp.1 w.2).1
      · exact (hFv (l, w)).trans hp
  have hcardS : ({v | v ∈ W ∧ hf (Fintype.card K) M v v = a} : Set (Fin n → L)).ncard =
      (Finset.univ.filter (fun p : L × (valPerp (Fintype.card K) M W e) =>
        p.1 ^ (Fintype.card K + 1) * (hf (Fintype.card K) M e e) + hf (Fintype.card K) M (p.2 : Fin n → L) p.2 = a)).card := by
    rw [hS, Set.ncard_image_of_injective _ hFinj, Set.ncard_eq_toFinset_card']
    congr 1
    ext p
    simp
  have hcardP : ({v | v ∈ (valPerp (Fintype.card K) M W e) ∧ hf (Fintype.card K) M v v = a} : Set (Fin n → L)).ncard =
      (Finset.univ.filter (fun w : (valPerp (Fintype.card K) M W e) => hf (Fintype.card K) M (w : Fin n → L) w = a)).card := by
    have h3 : {v | v ∈ (valPerp (Fintype.card K) M W e) ∧ hf (Fintype.card K) M v v = a} =
        Subtype.val '' {w : (valPerp (Fintype.card K) M W e) | hf (Fintype.card K) M (w : Fin n → L) w = a} := by
      ext v
      simp only [Set.mem_setOf_eq, Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
      constructor
      · rintro ⟨hv, hva⟩
        exact ⟨hv, hva⟩
      · rintro ⟨hv, hva⟩
        exact ⟨hv, hva⟩
    rw [h3, Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_eq_toFinset_card']
    congr 1
    ext w
    simp
  have hinner : ∀ w : (valPerp (Fintype.card K) M W e), (∑ l : L, if l ^ (Fintype.card K + 1) * (hf (Fintype.card K) M e e) + hf (Fintype.card K) M (w : Fin n → L) w = a
      then (1 : ℤ) else 0) = if hf (Fintype.card K) M (w : Fin n → L) w = a then (1 : ℤ) else (Fintype.card K + 1) := by
    intro w
    have ht : (a - hf (Fintype.card K) M (w : Fin n → L) w) ^ Fintype.card K = a - hf (Fintype.card K) M (w : Fin n → L) w := by
      rw [frob_sub (K := K), ha, val_fixed h2 hM]
    have hfib := val_fibre h2 (hf (Fintype.card K) M e e) (a - hf (Fintype.card K) M (w : Fin n → L) w) hb hbq ht
    have h4 : (∑ l : L, if l ^ (Fintype.card K + 1) * (hf (Fintype.card K) M e e) + hf (Fintype.card K) M (w : Fin n → L) w = a
        then (1 : ℤ) else 0) = ((Finset.univ.filter (fun l : L =>
          l ^ (Fintype.card K + 1) * (hf (Fintype.card K) M e e) = a - hf (Fintype.card K) M (w : Fin n → L) w)).card : ℤ) := by
      rw [Finset.card_filter]
      push_cast
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [eq_sub_iff_add_eq]
    rw [h4]
    have h5 : ((Finset.univ.filter (fun l : L =>
          l ^ (Fintype.card K + 1) * (hf (Fintype.card K) M e e) = a - hf (Fintype.card K) M (w : Fin n → L) w)).card : ℤ) =
        ((if a - hf (Fintype.card K) M (w : Fin n → L) w = 0 then 1 else Fintype.card K + 1 : ℕ) : ℤ) := by
      rw [← hfib]
    rw [h5]
    by_cases hc : hf (Fintype.card K) M (w : Fin n → L) w = a
    · have h6 : a - hf (Fintype.card K) M (w : Fin n → L) w = 0 := by rw [hc, sub_self]
      rw [if_pos h6, if_pos hc]
      norm_num
    · have h6 : a - hf (Fintype.card K) M (w : Fin n → L) w ≠ 0 := sub_ne_zero.2 (Ne.symm hc)
      rw [if_neg h6, if_neg hc]
      push_cast
      ring
  have hprod : ((Finset.univ.filter (fun p : L × (valPerp (Fintype.card K) M W e) =>
        p.1 ^ (Fintype.card K + 1) * (hf (Fintype.card K) M e e) + hf (Fintype.card K) M (p.2 : Fin n → L) p.2 = a)).card : ℤ) =
      ∑ w : (valPerp (Fintype.card K) M W e), if hf (Fintype.card K) M (w : Fin n → L) w = a then (1 : ℤ) else (Fintype.card K + 1) := by
    rw [Finset.card_filter]
    push_cast
    rw [Fintype.sum_prod_type_right]
    exact Finset.sum_congr rfl fun w _ => hinner w
  have hc2 : ((Finset.univ.filter (fun w : (valPerp (Fintype.card K) M W e) => hf (Fintype.card K) M (w : Fin n → L) w = a)).card : ℤ) =
      ∑ w : (valPerp (Fintype.card K) M W e), if hf (Fintype.card K) M (w : Fin n → L) w = a then (1 : ℤ) else 0 := by
    rw [Finset.card_filter]
    push_cast
    rfl
  have hcardP' : (Fintype.card (valPerp (Fintype.card K) M W e) : ℤ) = (Fintype.card L : ℤ) ^ finrank L (valPerp (Fintype.card K) M W e) := by
    exact_mod_cast Module.card_eq_pow_finrank (K := L) (V := (valPerp (Fintype.card K) M W e))
  rw [hcardS, hcardP, hprod, hc2, ← hcardP', Finset.mul_sum, ← Finset.sum_add_distrib]
  have h7 : ∀ w : (valPerp (Fintype.card K) M W e), ((if hf (Fintype.card K) M (w : Fin n → L) w = a then (1 : ℤ) else (Fintype.card K + 1)) +
      (Fintype.card K : ℤ) * (if hf (Fintype.card K) M (w : Fin n → L) w = a then (1 : ℤ) else 0)) = (Fintype.card K + 1) := by
    intro w
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun w _ => h7 w, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

open Classical in
theorem val_main (h2 : finrank K L = 2) (hM : IsHerm (Fintype.card K) M) :
    ∀ (d : ℕ) (W : Submodule L (Fin n → L)), NonDeg (Fintype.card K) M W →
      finrank L W = d → ∀ a : L, a ^ Fintype.card K = a →
        ((({v | v ∈ W ∧ hf (Fintype.card K) M v v = a} : Set (Fin n → L)).ncard : ℕ) : ℤ) =
          if a = 0 then valZ (Fintype.card K) d else valN (Fintype.card K) d := by
  intro d
  induction d with
  | zero =>
    intro W hW hd a ha
    have hW0 : W = ⊥ := by
      first
        | exact Submodule.finrank_eq_zero.mp hd
        | exact finrank_eq_zero.mp hd
    subst hW0
    have h00 : hf (Fintype.card K) M 0 0 = 0 := by
      first
        | simp [hf]
        | (unfold hf; simp [Fintype.card_ne_zero])
    by_cases ha0 : a = 0
    · subst ha0
      have hs : {v | v ∈ (⊥ : Submodule L (Fin n → L)) ∧ hf (Fintype.card K) M v v = 0} =
          ({0} : Set (Fin n → L)) := by
        ext v
        simp only [Submodule.mem_bot, Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · exact fun h => h.1
        · rintro rfl
          exact ⟨rfl, h00⟩
      rw [hs, Set.ncard_singleton, if_pos rfl]
      simp [valZ]
    · have hs : {v | v ∈ (⊥ : Submodule L (Fin n → L)) ∧ hf (Fintype.card K) M v v = a} =
          (∅ : Set (Fin n → L)) := by
        ext v
        simp only [Submodule.mem_bot, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
          not_and]
        rintro rfl
        rw [h00]
        exact fun h => ha0 h.symm
      rw [hs, Set.ncard_empty, if_neg ha0]
      simp [valN]
  | succ d ih =>
    intro W hW hd a ha
    have hne : W ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hd
      omega
    obtain ⟨e, he, hb⟩ := val_aniso h2 hM hW hne
    have hrec := val_recursion h2 hM he hb a ha
    have hfr : finrank L (valPerp (Fintype.card K) M W e) = d := by
      have h := finrank_valPerp (q := Fintype.card K) (M := M) he hb
      omega
    have hih := ih (valPerp (Fintype.card K) M W e) (nondeg_valPerp h2 hM hW he hb) hfr a ha
    have hcardL : (Fintype.card L : ℤ) = (Fintype.card K : ℤ) ^ 2 := by
      have h := Module.card_eq_pow_finrank (K := K) (V := L)
      rw [h2] at h
      exact_mod_cast h
    rw [hfr, hcardL, hih] at hrec
    split_ifs with ha0
    · rw [if_pos ha0] at hrec
      have h := valZ_succ (Fintype.card K) d
      linarith
    · rw [if_neg ha0] at hrec
      have h := valN_succ (Fintype.card K) d
      linarith

end

theorem valuation_count : ValCount := by
  intro K L _ _ _ _ _ h2 n M W hM hW a ha
  first
  | exact val_main h2 hM _ W hW rfl a ha
  | convert val_main h2 hM _ W hW rfl a ha

end DensInertW
