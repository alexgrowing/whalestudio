import Mathlib
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExceptionalPrimesFiniteCardLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardPowEqOneLeOfIsCyclicUnits

open Finset

namespace GlobalTheory

theorem card_class_in_dyadic_le (Y : ℝ) (hY : 0 ≤ Y) (M : ℕ) (hM : 0 < M) (T : Finset ℕ)
    (hT : ∀ g ∈ T, Y ≤ g ∧ (g : ℝ) ≤ 2 * Y)
    (hc : ∀ g ∈ T, ∀ g' ∈ T, g ≡ g' [MOD M]) : (T.card : ℝ) ≤ Y / M + 1 := by
  classical
  rcases T.eq_empty_or_nonempty with rfl | hne
  · have hMr : (0 : ℝ) < M := by exact_mod_cast hM
    rw [Finset.card_empty, Nat.cast_zero]
    have := div_nonneg hY hMr.le
    linarith
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have ha := T.min'_mem hne
  have key : ∀ g ∈ T, T.min' hne ≤ g ∧ M ∣ g - T.min' hne := fun g hg =>
    ⟨T.min'_le g hg, (Nat.modEq_iff_dvd' (T.min'_le g hg)).1 (hc _ ha g hg)⟩
  have hmaps : ∀ g ∈ T, (g - T.min' hne) / M ∈ Finset.range (⌊Y / M⌋₊ + 1) := by
    intro g hg
    rw [Finset.mem_range, Nat.lt_succ_iff]
    apply Nat.le_floor
    rw [le_div_iff₀ hMr]
    have h1 : (g - T.min' hne) / M * M ≤ g - T.min' hne := Nat.div_mul_le_self _ _
    have h2 : ((g - T.min' hne : ℕ) : ℝ) = g - T.min' hne := Nat.cast_sub (key g hg).1
    have h3 := (hT g hg).2
    have h4 := (hT _ ha).1
    calc (((g - T.min' hne) / M : ℕ) : ℝ) * M = (((g - T.min' hne) / M * M : ℕ) : ℝ) := by
          rw [Nat.cast_mul]
      _ ≤ ((g - T.min' hne : ℕ) : ℝ) := by exact_mod_cast h1
      _ ≤ Y := by rw [h2]; linarith
  have hinj : Set.InjOn (fun g => (g - T.min' hne) / M) T := by
    intro g hg g' hg' h
    have h' : (g - T.min' hne) / M = (g' - T.min' hne) / M := h
    have e1 := Nat.div_mul_cancel (key g hg).2
    have e2 := Nat.div_mul_cancel (key g' hg').2
    have e3 : g - T.min' hne = g' - T.min' hne := by rw [← e1, ← e2, h']
    have := (key g hg).1
    have := (key g' hg').1
    omega
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Finset.card_range] at hcard
  calc (T.card : ℝ) ≤ ((⌊Y / M⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ Y / M + 1 := by
        push_cast
        linarith [Nat.floor_le (div_nonneg hY hMr.le)]

theorem div_le_rpow_three_quarters (Y M : ℝ) (hY : 0 < Y) (hM : 0 < M) (h : Y < M ^ 4) :
    Y / M ≤ Y ^ ((3 : ℝ) / 4) := by
  have hq : 0 < Y ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hY _
  have h4 : (Y ^ ((1 : ℝ) / 4)) ^ 4 = Y := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hY.le]
    norm_num
  have hlt : Y ^ ((1 : ℝ) / 4) < M := by
    have : (Y ^ ((1 : ℝ) / 4)) ^ 4 < M ^ 4 := by rw [h4]; exact h
    exact lt_of_pow_lt_pow_left₀ 4 hM.le this
  have e : Y ^ ((3 : ℝ) / 4) = Y / Y ^ ((1 : ℝ) / 4) := by
    rw [show (3 : ℝ) / 4 = 1 - 1 / 4 by norm_num, Real.rpow_sub hY, Real.rpow_one]
  rw [e]
  exact div_le_div_of_nonneg_left hY.le hq hlt.le

theorem card_exc_fixed_le (hR : Formalism.CyclotomicNorms.RootsOfUnityCount) (Y : ℝ) (hY : 2 ≤ Y) (ℓ d : ℕ)
    (hd : 1 ≤ d) (T : Finset ℕ)
    (hT : ∀ g ∈ T, Y ≤ g ∧ (g : ℝ) ≤ 2 * Y ∧ Formalism.CyclotomicNorms.Exc g d ℓ) :
    (T.card : ℝ) ≤ 2 * d * (Y ^ ((3 : ℝ) / 4) + 1) := by
  classical
  have hY0 : 0 ≤ Y ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (by linarith) _
  rcases T.eq_empty_or_nonempty with rfl | hne
  · rw [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (by positivity) (by linarith)
  obtain ⟨g0, hg0, hmin⟩ := T.exists_min_image (fun g => padicValNat ℓ (g ^ d - 1)) hne
  obtain ⟨w, hw⟩ : ∃ w, w = padicValNat ℓ (g0 ^ d - 1) := ⟨_, rfl⟩
  have hmin' : ∀ g ∈ T, w ≤ padicValNat ℓ (g ^ d - 1) := by
    intro g hg
    rw [hw]
    exact hmin g hg
  have hg1 : ∀ g ∈ T, 1 ≤ g := fun g hg => by
    have h := (hT g hg).1
    have : (1 : ℝ) ≤ g := by linarith
    exact_mod_cast this
  have hgd : ∀ g ∈ T, 1 ≤ g ^ d := fun g hg => Nat.one_le_pow _ _ (hg1 g hg)
  obtain ⟨hℓ, hlt0⟩ := (hT g0 hg0).2.2
  rw [← hw] at hlt0
  have hw1 : 1 ≤ w := by
    by_contra h0
    have h00 : w = 0 := by omega
    rw [h00, mul_zero, pow_zero] at hlt0
    have := hgd g0 hg0
    omega
  have hM0 : 0 < ℓ ^ w := pow_pos hℓ.pos _
  have : NeZero (ℓ ^ w) := ⟨hM0.ne'⟩
  have hroot : ∀ g ∈ T, ((g : ZMod (ℓ ^ w))) ^ d = 1 := by
    intro g hg
    have h1 : ℓ ^ w ∣ g ^ d - 1 := (pow_dvd_pow ℓ (hmin' g hg)).trans pow_padicValNat_dvd
    have h2 : 1 ≡ g ^ d [MOD ℓ ^ w] := (Nat.modEq_iff_dvd' (hgd g hg)).2 h1
    have h3 := (ZMod.natCast_eq_natCast_iff 1 (g ^ d) (ℓ ^ w)).2 h2
    push_cast at h3
    exact h3.symm
  have hYM : Y < ((ℓ ^ w : ℕ) : ℝ) ^ 4 := by
    have h1 : (g0 : ℝ) ≤ ((g0 ^ d : ℕ) : ℝ) := by exact_mod_cast Nat.le_self_pow (by omega) g0
    have h2 : g0 ^ d < (ℓ ^ w) ^ 4 := by rw [← pow_mul, mul_comm]; exact hlt0
    have h3 : ((g0 ^ d : ℕ) : ℝ) < (((ℓ ^ w) ^ 4 : ℕ) : ℝ) := by exact_mod_cast h2
    rw [Nat.cast_pow (ℓ ^ w) 4] at h3
    linarith [(hT g0 hg0).1]
  have hfib : ∀ a ∈ T.image (fun g : ℕ => (g : ZMod (ℓ ^ w))),
      ((T.filter fun g : ℕ => (g : ZMod (ℓ ^ w)) = a).card : ℝ) ≤ Y ^ ((3 : ℝ) / 4) + 1 := by
    intro a _
    have h1 := card_class_in_dyadic_le Y (by linarith) (ℓ ^ w) hM0
      (T.filter fun g : ℕ => (g : ZMod (ℓ ^ w)) = a)
      (fun g hg => ⟨(hT g (Finset.mem_filter.1 hg).1).1, (hT g (Finset.mem_filter.1 hg).1).2.1⟩)
      (fun g hg g' hg' => (ZMod.natCast_eq_natCast_iff g g' (ℓ ^ w)).1
        ((Finset.mem_filter.1 hg).2.trans (Finset.mem_filter.1 hg').2.symm))
    have h2 := div_le_rpow_three_quarters Y ((ℓ ^ w : ℕ) : ℝ) (by linarith)
      (by exact_mod_cast hM0) hYM
    linarith
  have himg : (T.image fun g : ℕ => (g : ZMod (ℓ ^ w))).card ≤ 2 * d := by
    have hsub : T.image (fun g : ℕ => (g : ZMod (ℓ ^ w))) ⊆
        Finset.univ.filter (fun x : ZMod (ℓ ^ w) => x ^ d = 1) := by
      intro x hx
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hroot g hg⟩
    refine (Finset.card_le_card hsub).trans ?_
    have h1 := (hR ℓ w d hℓ hw1 hd).2
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h1
    exact h1
  rw [Finset.card_eq_sum_card_image (fun g : ℕ => (g : ZMod (ℓ ^ w))) T]
  push_cast
  calc ∑ a ∈ T.image (fun g : ℕ => (g : ZMod (ℓ ^ w))),
        ((T.filter fun g : ℕ => (g : ZMod (ℓ ^ w)) = a).card : ℝ)
      ≤ ∑ a ∈ T.image (fun g : ℕ => (g : ZMod (ℓ ^ w))), (Y ^ ((3 : ℝ) / 4) + 1) :=
        Finset.sum_le_sum hfib
    _ = ((T.image fun g : ℕ => (g : ZMod (ℓ ^ w))).card : ℝ) * (Y ^ ((3 : ℝ) / 4) + 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * d * (Y ^ ((3 : ℝ) / 4) + 1) := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        exact_mod_cast himg

theorem card_mem_BB_fixed_le (hR : Formalism.CyclotomicNorms.RootsOfUnityCount) (Y : ℝ) (hY : 2 ≤ Y) (ℓ N : ℕ)
    (T : Finset ℕ) (hT : ∀ g ∈ T, Y ≤ g ∧ (g : ℝ) ≤ 2 * Y ∧ ℓ ∈ Formalism.CyclotomicNorms.BB N g) :
    (T.card : ℝ) ≤ 1 + 2 * N ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1) := by
  classical
  have hY0 : 0 ≤ Y ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (by linarith) _
  have hsub : T ⊆ T.filter (fun g => g = ℓ) ∪
      (Finset.Icc 1 N).biUnion (fun d => T.filter (fun g => Formalism.CyclotomicNorms.Exc g d ℓ)) := by
    intro g hg
    have h := (hT g hg).2.2
    simp only [Formalism.CyclotomicNorms.BB, Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq] at h
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_biUnion]
    rcases h with h | ⟨d, hd1, hdN, hex⟩
    · exact Or.inl ⟨hg, h.symm⟩
    · exact Or.inr ⟨d, Finset.mem_Icc.2 ⟨hd1, hdN⟩, Finset.mem_filter.2 ⟨hg, hex⟩⟩
  have h0 : (T.filter (fun g => g = ℓ)).card ≤ 1 := by
    apply Finset.card_le_one.2
    intro a ha b hb
    rw [(Finset.mem_filter.1 ha).2, (Finset.mem_filter.1 hb).2]
  have hd : ∀ d ∈ Finset.Icc 1 N, ((T.filter (fun g => Formalism.CyclotomicNorms.Exc g d ℓ)).card : ℝ) ≤
      2 * N * (Y ^ ((3 : ℝ) / 4) + 1) := by
    intro d hdm
    obtain ⟨hd1, hdN⟩ := Finset.mem_Icc.1 hdm
    have h1 := card_exc_fixed_le hR Y hY ℓ d hd1 (T.filter (fun g => Formalism.CyclotomicNorms.Exc g d ℓ))
      (fun g hg => ⟨(hT g (Finset.mem_filter.1 hg).1).1, (hT g (Finset.mem_filter.1 hg).1).2.1,
        (Finset.mem_filter.1 hg).2⟩)
    have hdN' : (d : ℝ) ≤ N := by exact_mod_cast hdN
    have h2 := mul_le_mul_of_nonneg_right hdN' (by linarith : (0 : ℝ) ≤ Y ^ ((3 : ℝ) / 4) + 1)
    linarith
  have hc1 : T.card ≤ (T.filter (fun g => g = ℓ)).card +
      ∑ d ∈ Finset.Icc 1 N, (T.filter (fun g => Formalism.CyclotomicNorms.Exc g d ℓ)).card :=
    (Finset.card_le_card hsub).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _))
  have hc2 : (T.card : ℝ) ≤
      1 + ∑ d ∈ Finset.Icc 1 N, ((T.filter (fun g => Formalism.CyclotomicNorms.Exc g d ℓ)).card : ℝ) := by
    have h1 := (Nat.cast_le (α := ℝ)).2 hc1
    push_cast at h1
    have h0' : ((T.filter (fun g => g = ℓ)).card : ℝ) ≤ 1 := by exact_mod_cast h0
    linarith
  have hc3 : ∑ d ∈ Finset.Icc 1 N, ((T.filter (fun g => Formalism.CyclotomicNorms.Exc g d ℓ)).card : ℝ) ≤
      N * (2 * N * (Y ^ ((3 : ℝ) / 4) + 1)) := by
    calc _ ≤ ∑ d ∈ Finset.Icc 1 N, 2 * (N : ℝ) * (Y ^ ((3 : ℝ) / 4) + 1) := Finset.sum_le_sum hd
      _ = N * (2 * N * (Y ^ ((3 : ℝ) / 4) + 1)) := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  have e : (N : ℝ) * (2 * N * (Y ^ ((3 : ℝ) / 4) + 1)) = 2 * N ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1) := by
    ring
  linarith

theorem choiceCount_of (hB : Formalism.CyclotomicNorms.BBCount) (hR : Formalism.CyclotomicNorms.RootsOfUnityCount) :
    Formalism.CyclotomicNorms.ChoiceCount := by
  intro Y N g₁ hY hN hg₁ hg₁' S hS
  classical
  have h2 : 2 ≤ g₁ := by
    have : (2 : ℝ) ≤ g₁ := by linarith
    exact_mod_cast this
  obtain ⟨hfin, hcard⟩ := (hB g₁ h2).2 N
  have hsub : S ⊆ hfin.toFinset.biUnion (fun ℓ => S.filter (fun g => ℓ ∈ Formalism.CyclotomicNorms.BB N g)) := by
    intro g hg
    obtain ⟨ℓ, hℓ1, hℓ2⟩ := (hS g hg).2.2
    exact Finset.mem_biUnion.2 ⟨ℓ, hfin.mem_toFinset.2 hℓ2, Finset.mem_filter.2 ⟨hg, hℓ1⟩⟩
  have hbound : ∀ ℓ ∈ hfin.toFinset, ((S.filter (fun g => ℓ ∈ Formalism.CyclotomicNorms.BB N g)).card : ℝ) ≤
      1 + 2 * N ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1) := fun ℓ _ =>
    card_mem_BB_fixed_le hR Y hY ℓ N _ (fun g hg => ⟨(hS g (Finset.mem_filter.1 hg).1).1,
      (hS g (Finset.mem_filter.1 hg).1).2.1, (Finset.mem_filter.1 hg).2⟩)
  have hFc : (hfin.toFinset.card : ℝ) ≤ 3 * N + 1 := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]
    exact_mod_cast hcard
  have hc : (S.card : ℝ) ≤
      ∑ ℓ ∈ hfin.toFinset, ((S.filter (fun g => ℓ ∈ Formalism.CyclotomicNorms.BB N g)).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hY0 : 0 ≤ Y ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (by linarith) _
  calc (S.card : ℝ) ≤ _ := hc
    _ ≤ ∑ ℓ ∈ hfin.toFinset, (1 + 2 * (N : ℝ) ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1)) :=
        Finset.sum_le_sum hbound
    _ = hfin.toFinset.card * (1 + 2 * (N : ℝ) ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (3 * N + 1) * (1 + 2 * N ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1)) :=
        mul_le_mul_of_nonneg_right hFc
          (add_nonneg zero_le_one (mul_nonneg (by positivity) (by linarith)))

theorem choice_count : Formalism.CyclotomicNorms.ChoiceCount := choiceCount_of exceptional_set_count rootsOfUnityCount

end GlobalTheory
