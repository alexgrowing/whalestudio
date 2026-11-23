import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DplusLeBeA
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.TypicalPathOrdersSmall
import Formalism.ThetaLogCoordinates.ResidueClassEstimates.FinalT

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.T

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas
open Formalism.InvariantFactorPaths

theorem filter_ge_get_eq_take : ∀ (L : List ℕ), L.Pairwise (· > ·) → ∀ (e : ℕ) (he : e < L.length),
    L.filter (fun y => decide (L[e] ≤ y)) = L.take (e + 1) := by
  intro L
  induction L with
  | nil => intro _ e he; simp at he
  | cons x xs ih =>
    intro hp e he
    rw [List.pairwise_cons] at hp
    cases e with
    | zero =>
      simp only [List.getElem_cons_zero, List.take_succ_cons, List.take_zero]
      rw [List.filter_cons_of_pos (by simp)]
      congr 1
      rw [List.filter_eq_nil_iff]
      intro y hy
      have h1 := hp.1 y hy
      simp only [decide_eq_true_eq, not_le]
      omega
    | succ e =>
      simp only [List.getElem_cons_succ, List.take_succ_cons]
      have hlt : xs[e]'(by simp at he; omega) < x := hp.1 _ (List.getElem_mem _)
      rw [List.filter_cons_of_pos (by simp only [decide_eq_true_eq]; omega),
        ih hp.2 e (by simp at he; omega)]

def latestList (P : ℕ → Bool) (M : ℕ) : List ℕ := ((List.range' 1 M).filter P).reverse

theorem mem_latest_list (P : ℕ → Bool) (M y : ℕ) : y ∈ latestList P M ↔ (1 ≤ y ∧ y ≤ M) ∧ P y = true := by
  simp only [latestList, List.mem_reverse, List.mem_filter, List.mem_range'_1]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1.1, by omega⟩, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1.1, by omega⟩, h2⟩

theorem latest_list_pairwise_gt (P : ℕ → Bool) (M : ℕ) : (latestList P M).Pairwise (· > ·) := by
  rw [latestList, List.pairwise_reverse]
  exact (List.pairwise_lt_range' (s := 1) (n := M)).filter _

theorem latest_list_nodup (P : ℕ → Bool) (M : ℕ) : (latestList P M).Nodup :=
  (latest_list_pairwise_gt P M).imp ne_of_gt

def countFrom (P : ℕ → Bool) (M x : ℕ) : ℕ := ((Finset.Icc 1 M).filter fun y => P y = true ∧ x ≤ y).card

theorem count_from_eq_filter_length (P : ℕ → Bool) (M x : ℕ) :
    countFrom P M x = ((latestList P M).filter fun y => decide (x ≤ y)).length := by
  unfold countFrom
  have hnd : ((latestList P M).filter fun y => decide (x ≤ y)).Nodup := (latest_list_nodup P M).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_Icc, List.mem_toFinset, List.mem_filter, mem_latest_list,
    decide_eq_true_eq]
  tauto

theorem latest_list_get_spec (P : ℕ → Bool) (M e : ℕ) (he : e < (latestList P M).length) :
    ((1 ≤ (latestList P M)[e] ∧ (latestList P M)[e] ≤ M) ∧ P (latestList P M)[e] = true) ∧
      countFrom P M (latestList P M)[e] = e + 1 := by
  refine ⟨(mem_latest_list P M _).1 (List.getElem_mem _), ?_⟩
  rw [count_from_eq_filter_length, filter_ge_get_eq_take _ (latest_list_pairwise_gt P M) e he, List.length_take]
  omega

theorem count_from_le_length (P : ℕ → Bool) (M x : ℕ) : countFrom P M x ≤ (latestList P M).length := by
  rw [count_from_eq_filter_length]
  exact List.length_filter_le _ _

theorem count_from_antitone (P : ℕ → Bool) (M : ℕ) {x x' : ℕ} (h : x ≤ x') : countFrom P M x' ≤ countFrom P M x := by
  unfold countFrom
  apply Finset.card_le_card
  intro y hy
  simp only [Finset.mem_filter] at hy ⊢
  exact ⟨hy.1, hy.2.1, le_trans h hy.2.2⟩

theorem count_from_strict_anti (P : ℕ → Bool) (M : ℕ) {x x' : ℕ} (h : x < x') (hx : (1 ≤ x ∧ x ≤ M) ∧ P x = true) :
    countFrom P M x' < countFrom P M x := by
  unfold countFrom
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (fun y hy => by
    simp only [Finset.mem_filter] at hy ⊢
    exact ⟨hy.1, hy.2.1, le_trans h.le hy.2.2⟩)]
  refine ⟨x, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨hx.1, hx.2, le_rfl⟩
  · simp only [Finset.mem_filter]
    intro hc
    exact absurd hc.2.2 (not_le.2 h)

theorem latest_list_get_of_count (P : ℕ → Bool) (M e x : ℕ) (hx : (1 ≤ x ∧ x ≤ M) ∧ P x = true) (hc : countFrom P M x = e + 1) :
    ∃ he : e < (latestList P M).length, (latestList P M)[e] = x := by
  obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.1 ((mem_latest_list P M x).2 hx)
  have h1 := (latest_list_get_spec P M i hi).2
  rw [hix, hc] at h1
  have hie : i = e := by omega
  subst hie
  exact ⟨hi, hix⟩

theorem latest_list_succ_lt (P : ℕ → Bool) (M e : ℕ) (he : e + 1 < (latestList P M).length) :
    (latestList P M)[e + 1] < (latestList P M)[e]'(by omega) := by
  exact List.pairwise_iff_getElem.1 (latest_list_pairwise_gt P M) e (e + 1) (by omega) he (by omega)

variable {N r K : ℕ}

def toL (r K : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) : BranchingDimensions.Letters where
  r := r
  K := K
  Ns := N
  vec := fun i => if h : 1 ≤ i ∧ i ≤ N then LL.vec ⟨i - 1, by omega⟩ else true
  B := fun i => if h : 1 ≤ i ∧ i ≤ N then B ⟨i - 1, by omega⟩ else 0

theorem toL_vec (LL : Letters (Fin N)) (B : Fin N → ℕ) (i : ℕ) (h : 1 ≤ i ∧ i ≤ N) :
    (toL r K LL B).vec i = LL.vec ⟨i - 1, by omega⟩ := by
  simp only [toL]
  rw [dif_pos h]

theorem toL_B (LL : Letters (Fin N)) (B : Fin N → ℕ) (i : ℕ) (h : 1 ≤ i ∧ i ≤ N) :
    (toL r K LL B).B i = B ⟨i - 1, by omega⟩ := by
  simp only [toL]
  rw [dif_pos h]

section
variable {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}

theorem letters_n0_eq (H : HypT N n0 r K LL B od bb a La p) : (toL r K LL B).n0 = n0 := by
  show N - r = n0
  have := H.hN
  omega

theorem toL_Wf [NeZero K] (H : HypT N n0 r K LL B od bb a La p) : (toL r K LL B).Wf := by
  have hn0 := letters_n0_eq (r := r) (K := K) H
  have hN := H.hN
  have h3 := H.two_r_le_n0
  refine ⟨H.r1, Nat.one_le_iff_ne_zero.2 (NeZero.ne K), ?_, fun i h1 h2 => ?_, fun i h1 h2 => ?_⟩
  · show 3 * r ≤ N
    omega
  · simp only [toL] at h2
    rw [toL_vec LL B i ⟨h1, by omega⟩]
    exact H.vec_true_of_early _ (by simp only; omega)
  · rw [hn0] at h1
    simp only [toL] at h2
    rw [toL_vec LL B i ⟨by omega, h2⟩]
    exact H.vec_true_of_late _ (by simp only; omega)

theorem latest_thresholds_decay (H : HypT N n0 r K LL B od bb a La p) (P : ℕ → Bool) (v : Bool)
    (hP : ∀ i (h : 1 ≤ i ∧ i ≤ N), P i = true → LL.vec ⟨i - 1, by omega⟩ = v) (l : ℕ)
    (hl : l + 1 < ((latestList P n0).map (toL r K LL B).B).length) :
    13 ^ 2 * ((latestList P n0).map (toL r K LL B).B).getD (l + 1) 0 ≤
      5 * ((latestList P n0).map (toL r K LL B).B).getD l 0 := by
  have hlen : l + 1 < (latestList P n0).length := by simpa using hl
  have e1 : ((latestList P n0).map (toL r K LL B).B).getD (l + 1) 0 =
      (toL r K LL B).B ((latestList P n0)[l + 1]) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, hlen]
  have e2 : ((latestList P n0).map (toL r K LL B).B).getD l 0 =
      (toL r K LL B).B ((latestList P n0)[l]'(by omega)) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, show l < (latestList P n0).length by omega]
  rw [e1, e2]
  have hxy := latest_list_succ_lt P n0 l hlen
  have hxs := (latest_list_get_spec P n0 (l + 1) hlen).1
  have hys := (latest_list_get_spec P n0 l (by omega)).1
  generalize (latestList P n0)[l + 1] = x at hxy hxs ⊢
  generalize (latestList P n0)[l]'(by omega) = y at hxy hys ⊢
  have hN := H.hN
  rw [toL_B LL B x ⟨hxs.1.1, by omega⟩, toL_B LL B y ⟨hys.1.1, by omega⟩]
  have hv : LL.vec ⟨x - 1, by omega⟩ = LL.vec ⟨y - 1, by omega⟩ := by
    rw [hP x ⟨hxs.1.1, by omega⟩ hxs.2, hP y ⟨hys.1.1, by omega⟩ hys.2]
  have h2 := H.H2 ⟨x - 1, by omega⟩ ⟨y - 1, by omega⟩
    (by rw [Fin.lt_iff_val_lt_val]; simp only; omega) (by simp only; omega) hv
  have hp13 : (13 : ℝ) ≤ p := by exact_mod_cast H.p13
  have hB0 : (0 : ℝ) ≤ (B ⟨x - 1, by omega⟩ : ℝ) := Nat.cast_nonneg _
  have h3 : ((13 ^ 2 * B ⟨x - 1, by omega⟩ : ℕ) : ℝ) ≤ ((5 * B ⟨y - 1, by omega⟩ : ℕ) : ℝ) := by
    push_cast
    have hp2 : (169 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
    have h8 := mul_le_mul_of_nonneg_right hp2 hB0
    linarith
  exact_mod_cast h3

theorem toL_Hyp [NeZero K] (H : HypT N n0 r K LL B od bb a La p) : (toL r K LL B).Hyp a 13 := by
  have hn0 := letters_n0_eq (r := r) (K := K) H
  have hN := H.hN
  have h3n := H.two_r_le_n0
  have h3K := H.N_add_r_le_K
  have h4 := H.H4
  have h4a := H.N_le_a
  have eV : (toL r K LL B).latestV (toL r K LL B).n0 =
      (latestList (fun l => (toL r K LL B).vec l) n0).map (toL r K LL B).B := by
    simp only [BranchingDimensions.Letters.latestV, latestList, hn0, min_self]
  have eC : (toL r K LL B).latestC (toL r K LL B).n0 =
      (latestList (fun l => !(toL r K LL B).vec l) n0).map (toL r K LL B).B := by
    simp only [BranchingDimensions.Letters.latestC, latestList, hn0, min_self]
  refine ⟨H.a3, by norm_num, le_rfl, fun i h1 h2 => ?_, fun l hl => ?_, fun l hl => ?_,
    fun i h1 h2 => ?_, ?_, ?_, ?_, ?_⟩
  · rw [hn0] at h2
    rw [toL_B LL B i ⟨h1, by omega⟩]
    have h5 := H.H1 ⟨i - 1, by omega⟩ (by simp only; omega)
    refine ⟨?_, h5.2⟩
    show r + K ≤ B ⟨i - 1, by omega⟩
    exact_mod_cast h5.1
  · rw [eV] at hl ⊢
    exact latest_thresholds_decay H _ true (fun i hi hPi => by rw [← toL_vec LL B i hi]; exact hPi) l hl
  · rw [eC] at hl ⊢
    exact latest_thresholds_decay H _ false (fun i hi hPi => by
      rw [← toL_vec LL B i hi]
      simpa using hPi) l hl
  · rw [hn0] at h1 h2
    simp only [toL] at h1
    rw [toL_vec LL B i ⟨by omega, by omega⟩]
    exact H.vec_true_of_late _ (by simp only; omega)
  · show N + r ≤ K
    omega
  · show 2 * r ≤ N
    omega
  · show r + K ≤ 2 * (K - 2 * N)
    have hK : 2 * N ≤ K := by
      have h6 : (2 * N : ℝ) ≤ K := by
        have : (0 : ℝ) ≤ ((r + K : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
      exact_mod_cast h6
    have h7 : ((r + K : ℕ) : ℝ) ≤ ((2 * (K - 2 * N) : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_sub hK]
      push_cast at h4 ⊢
      linarith
    exact_mod_cast h7
  · show (N : ℝ) ≤ a
    exact h4a

def toB (bb : Fin N → ℝ) (p : ℕ) : ℕ → ℝ := fun i =>
  if h : 1 ≤ i ∧ i ≤ N then 13 * bb ⟨i - 1, by omega⟩ / (p : ℝ) else 1

theorem toL_TData (H : HypT N n0 r K LL B od bb a La p) : (toL r K LL B).TData 13 La (toB bb p) := by
  have hN := H.hN
  have hp : (0 : ℝ) < p := by
    have := H.p13
    exact_mod_cast (by omega : 0 < p)
  refine ⟨H.La_pos, fun i h1 h2 => ?_⟩
  simp only [toL] at h1 h2
  have hi : 1 ≤ i ∧ i ≤ N := ⟨by omega, h2⟩
  have hb : toB bb p i = 13 * bb ⟨i - 1, by omega⟩ / (p : ℝ) := by
    simp only [toB]
    rw [dif_pos hi]
  refine ⟨?_, fun l hl1 hl2 hl3 => ?_⟩
  · rw [hb]
    have := H.bb_pos ⟨i - 1, by omega⟩ (by simp only; omega)
    positivity
  · rw [letters_n0_eq H] at hl3
    rw [toL_B LL B l ⟨hl1, by omega⟩, hb]
    have h5 := H.bb_le ⟨i - 1, by omega⟩ ⟨l - 1, by omega⟩ (by simp only; omega)
      (by rw [Fin.lt_iff_val_lt_val]; simp only; omega) (by simp only; omega)
    refine le_trans h5 (le_of_eq ?_)
    push_cast
    ring

end

end Formalism.MainNotions.SelectionLemmas.Pf.T
