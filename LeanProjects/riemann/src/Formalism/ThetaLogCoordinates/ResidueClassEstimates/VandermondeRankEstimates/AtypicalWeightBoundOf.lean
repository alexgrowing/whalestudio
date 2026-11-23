import Formalism.ThetaLogCoordinates.ResidueClassEstimates.StatementT

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.BranchingDimensions

open Letters

namespace TTyp

end TTyp

private theorem le_div_of_mul_le_of_pos' {x y z : ℝ} (hz : 0 < z) (h : x * z ≤ y) : x ≤ y / z := by
  have hz' : z ≠ 0 := ne_of_gt hz
  have e : y / z * z = y := by field_simp
  nlinarith

namespace TTyp

lemma be_le (D : Letters) {a : ℝ} (ha : 0 ≤ a) (h : ∀ i, 1 ≤ i → i ≤ D.n0 → (D.B i : ℝ) ≤ 2 * a) :
    (D.be : ℝ) ≤ 2 * a * D.Ns := by
  unfold Formalism.InvariantFactorPaths.BranchingDimensions.Letters.be
  push_cast
  have hn : (D.n0 : ℝ) ≤ D.Ns := by
    unfold Formalism.InvariantFactorPaths.BranchingDimensions.Letters.n0
    exact_mod_cast Nat.sub_le _ _
  calc (∑ i ∈ Icc 1 D.n0, (D.B i : ℝ)) ≤ ∑ i ∈ Icc 1 D.n0, 2 * a :=
        Finset.sum_le_sum (fun i hi => by
          rw [Finset.mem_Icc] at hi
          exact h i hi.1 hi.2)
    _ = (D.n0 : ℝ) * (2 * a) := by simp
    _ ≤ 2 * a * D.Ns := by nlinarith

lemma be_eq (D : Letters) : D.be = D.bePos + D.beNeg := by
  unfold Formalism.InvariantFactorPaths.BranchingDimensions.Letters.be Formalism.InvariantFactorPaths.BranchingDimensions.Letters.bePos Formalism.InvariantFactorPaths.BranchingDimensions.Letters.beNeg
  rw [← Finset.sum_filter_add_sum_filter_not (Icc 1 D.n0) (fun i => D.vec i = true)]
  simp only [Bool.not_eq_true]

lemma ent_sign (h20 : PathEntryBounds) {D : Letters} {mu : D.Stages} (hW : D.Wf) (hP : D.IsPATH mu)
    {i m : ℕ} (hi : i ≤ D.Ns) (hm : m < D.k) :
    (m + D.Ns < D.k → 0 ≤ ent mu i m) ∧ (D.Ns ≤ m → ent mu i m ≤ 0) := by
  unfold Formalism.InvariantFactorPaths.BranchingDimensions.PathEntryBounds at h20
  have H := (h20 D mu hW hP).2 i hi
  have hv : D.nVec i ≤ D.Ns := by
    unfold Formalism.InvariantFactorPaths.BranchingDimensions.Letters.nVec
    calc _ ≤ (Icc 1 i).card := Finset.card_filter_le _ _
      _ = i := by simp
      _ ≤ D.Ns := hi
  have hc : D.nCov i ≤ D.Ns := by
    unfold Formalism.InvariantFactorPaths.BranchingDimensions.Letters.nCov
    calc _ ≤ (Icc 1 i).card := Finset.card_filter_le _ _
      _ = i := by simp
      _ ≤ D.Ns := hi
  exact ⟨fun h1 => H.2 m (by omega), fun h1 => H.1 m (by omega) hm⟩

end TTyp

namespace TTyp

def lat (q : ℕ → Bool) (B : ℕ → ℕ) (i : ℕ) : List ℕ := (((List.range' 1 i).filter q).reverse).map B

private theorem list_range'_succ_eq_append_singleton (s n : ℕ) : List.range' s (n + 1) = List.range' s n ++ [s + n] := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    show s :: List.range' (s + 1) (n + 1) = (s :: List.range' (s + 1) n) ++ [s + (n + 1)]
    rw [ih (s + 1), show s + 1 + n = s + (n + 1) by omega]
    rfl

lemma lat_succ (q : ℕ → Bool) (B : ℕ → ℕ) (i : ℕ) :
    lat q B (i + 1) = if q (i + 1) = true then B (i + 1) :: lat q B i else lat q B i := by
  unfold lat
  rw [list_range'_succ_eq_append_singleton, show (1 : ℕ) + i = i + 1 from Nat.add_comm 1 i, List.filter_append]
  by_cases hq : q (i + 1) = true
  · simp [hq]
  · simp [hq]

private theorem list_sum_drop_eq_getD_add_sum_drop_succ (l : List ℕ) (u : ℕ) : (l.drop u).sum = l.getD u 0 + (l.drop (u + 1)).sum := by
  induction l generalizing u with
  | nil => simp
  | cons x l ih =>
    cases u with
    | zero => simp
    | succ u => simpa using ih u

lemma sum_drop : ∀ (l : List ℕ) (u : ℕ), (l.drop u).sum = ∑ j ∈ Ico u l.length, l.getD j 0
  | [], u => by simp
  | a :: t, 0 => by
      have e := Finset.sum_Ico_add' (fun j => (a :: t).getD j 0) 0 t.length 1
      have h := sum_drop t 0
      simp only [List.drop_zero, List.getD_cons_succ, zero_add] at e h
      rw [List.drop_zero, List.sum_cons, List.length_cons,
        Finset.sum_eq_sum_Ico_succ_bot (by omega), zero_add, ← e, h, List.getD_cons_zero]
  | a :: t, u + 1 => by
      have e := Finset.sum_Ico_add' (fun j => (a :: t).getD j 0) u t.length 1
      simp only [List.getD_cons_succ] at e
      rw [List.drop_succ_cons, List.length_cons, ← e, sum_drop t u]

lemma sum_lat (g : ℕ → ℝ) (q : ℕ → Bool) (B : ℕ → ℕ) : ∀ n,
    ∑ l ∈ range (lat q B n).length, g ((lat q B n).getD l 0) =
      ∑ i ∈ (Icc 1 n).filter (fun i => q i = true), g (B i)
  | 0 => by simp [lat]
  | n + 1 => by
      rw [lat_succ, Finset.sum_filter, Finset.sum_Icc_succ_top (by omega), ← Finset.sum_filter,
        ← sum_lat g q B n]
      by_cases h : q (n + 1) = true
      · simp only [if_pos h, List.length_cons, Finset.sum_range_succ', List.getD_cons_succ,
          List.getD_cons_zero]
      · simp only [if_neg h, add_zero]

lemma lat_split (q : ℕ → Bool) (B : ℕ → ℕ) (i : ℕ) : ∀ d, ∃ pre : List ℕ,
    lat q B (i + d) = pre ++ lat q B i ∧
    pre.length = ((Icc (i + 1) (i + d)).filter (fun l => q l = true)).card
  | 0 => ⟨[], by simp, by simp⟩
  | d + 1 => by
      obtain ⟨pre, h1, h2⟩ := lat_split q B i d
      rw [← add_assoc, lat_succ, Finset.card_filter, Finset.sum_Icc_succ_top (by omega),
        ← Finset.card_filter]
      by_cases h : q (i + d + 1) = true
      · exact ⟨B (i + d + 1) :: pre, by simp [h, h1], by simp [h, h2]⟩
      · exact ⟨pre, by simp [h, h1], by simp [h, h2]⟩

lemma mem_lat {q : ℕ → Bool} {B : ℕ → ℕ} {j x : ℕ} (h : x ∈ lat q B j) :
    ∃ l, 1 ≤ l ∧ l ≤ j ∧ q l = true ∧ x = B l := by
  unfold lat at h
  simp only [List.mem_map, List.mem_reverse, List.mem_filter, List.mem_range'_1] at h
  obtain ⟨l, ⟨⟨h1, h2⟩, hq⟩, hx⟩ := h
  exact ⟨l, h1, by omega, hq, hx.symm⟩

lemma getD_mem {l : List ℕ} {t : ℕ} (h : t < l.length) : l.getD t 0 ∈ l := by
  induction l generalizing t with
  | nil => simp at h
  | cons x l ih =>
    cases t with
    | zero => simp
    | succ t =>
      rw [List.getD_cons_succ]
      exact List.mem_cons_of_mem _ (ih (by simpa using h))

private theorem list_getD_append_add_length (pre R : List ℕ) (u : ℕ) : (pre ++ R).getD (u + pre.length) 0 = R.getD u 0 := by
  induction pre with
  | nil => simp
  | cons x pre ih =>
    rw [List.length_cons, ← Nat.add_assoc, List.cons_append, List.getD_cons_succ]
    exact ih

lemma lat_shift (q : ℕ → Bool) (B : ℕ → ℕ) {i n : ℕ} (h : i ≤ n) :
    (∀ u, (lat q B n).getD (u + ((Icc (i + 1) n).filter (fun l => q l = true)).card) 0 =
      (lat q B i).getD u 0) ∧
    (lat q B n).length = ((Icc (i + 1) n).filter (fun l => q l = true)).card + (lat q B i).length := by
  obtain ⟨pre, hpre, hlen⟩ := lat_split q B i (n - i)
  rw [show i + (n - i) = n by omega] at hpre hlen
  refine ⟨fun u => ?_, ?_⟩
  · rw [hpre, ← hlen, list_getD_append_add_length]
  · rw [hpre, List.length_append, hlen]

lemma bracket (h31 : LogBinomialProperties) (h34 : LogBinomialDeficit) (k' K : ℕ) (la : ℕ → ℤ) (lst : List ℕ) (hk : 1 ≤ k')
    (h1 : ∀ l, l < lst.length → k' ≤ lst.getD l 0)
    (h2 : ∀ l, l + 1 < lst.length → 4 * lst.getD (l + 1) 0 ≤ lst.getD l 0)
    (h3 : ∀ u, tailPos K la u ≤ ((lst.drop u).sum : ℕ)) :
    (∑ m ∈ range K, fT k' ((max (la m) 0 : ℤ) : ℝ)) -
      (∑ l ∈ range lst.length, fT k' ((lst.getD l 0 : ℕ) : ℝ)) ≤ 0 ∧
    ∀ (u₀ : ℕ) (X : ℝ), 0 < X → ((tailPos K la u₀ : ℤ) : ℝ) ≤ (((lst.drop u₀).sum : ℕ) : ℝ) - X →
      u₀ < lst.length ∧
      (∑ m ∈ range K, fT k' ((max (la m) 0 : ℤ) : ℝ)) -
        (∑ l ∈ range lst.length, fT k' ((lst.getD l 0 : ℕ) : ℝ)) ≤
          -(X * k' / (4 * ((lst.getD u₀ 0 : ℕ) : ℝ))) := by
  classical
  have F0 : fT k' 0 = 0 := (h31 k').1
  have hnn : ∀ m, (0 : ℝ) ≤ ((max (la m) 0 : ℤ) : ℝ) := fun m => by exact_mod_cast le_max_right (la m) 0

  have hbeyond : ∀ m, m < K → lst.length ≤ m → max (la m) 0 = 0 := by
    intro m hmK hmL
    have h := h3 lst.length
    rw [List.drop_length] at h
    have h0 : tailPos K la lst.length ≤ 0 := by simpa using h
    have hsub : max (la m) 0 ≤ tailPos K la lst.length := by
      unfold tailPos
      exact Finset.single_le_sum (f := fun m => max (la m) 0) (fun i _ => le_max_right _ _)
        (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hmK, hmL⟩)
    exact le_antisymm (le_trans hsub h0) (le_max_right _ _)
  let al : ℕ → ℝ := fun l => if l < K then ((max (la l) 0 : ℤ) : ℝ) else 0
  let Bs : ℕ → ℝ := fun l => ((lst.getD l 0 : ℕ) : ℝ)
  have hal : ∀ l, al l = if l < K then ((max (la l) 0 : ℤ) : ℝ) else 0 := fun l => rfl
  have hBs : ∀ l, Bs l = ((lst.getD l 0 : ℕ) : ℝ) := fun l => rfl
  have hal0 : ∀ l, 0 ≤ al l := by
    intro l
    rw [hal]
    split_ifs
    · exact hnn l
    · exact le_refl 0
  have halK : ∀ l, K ≤ l → al l = 0 := by
    intro l hl
    rw [hal, if_neg (by omega)]
  have halL : ∀ l, lst.length ≤ l → al l = 0 := by
    intro l hl
    rw [hal]
    split_ifs with h
    · rw [hbeyond l h hl]
      simp
    · rfl
  have hA : ∀ u, ((tailPos K la u : ℤ) : ℝ) = ∑ l ∈ Ico u lst.length, al l := by
    intro u
    unfold tailPos
    rw [Int.cast_sum]
    have e1 : ∑ m ∈ (range K).filter (fun m => u ≤ m), ((max (la m) 0 : ℤ) : ℝ) =
        ∑ m ∈ (range K).filter (fun m => u ≤ m), al m := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mem_filter, Finset.mem_range] at hm
      rw [hal, if_pos hm.1]
    have e2 : ∑ m ∈ (range K).filter (fun m => u ≤ m), al m = ∑ m ∈ Ico u (K + lst.length), al m := by
      apply Finset.sum_subset
      · intro m hm
        rw [Finset.mem_filter, Finset.mem_range] at hm
        rw [Finset.mem_Ico]
        exact ⟨hm.2, by omega⟩
      · intro m hm hnm
        rw [Finset.mem_Ico] at hm
        apply halK
        by_contra hc
        exact hnm (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hm.1⟩)
    have e3 : ∑ m ∈ Ico u lst.length, al m = ∑ m ∈ Ico u (K + lst.length), al m := by
      apply Finset.sum_subset
      · intro m hm
        rw [Finset.mem_Ico] at hm ⊢
        exact ⟨hm.1, by omega⟩
      · intro m hm hnm
        rw [Finset.mem_Ico] at hm
        apply halL
        by_contra hc
        exact hnm (Finset.mem_Ico.mpr ⟨hm.1, by omega⟩)
    rw [e1, e2, e3]
  have hB : ∀ u, (((lst.drop u).sum : ℕ) : ℝ) = ∑ l ∈ Ico u lst.length, Bs l := by
    intro u
    rw [sum_drop lst u, Nat.cast_sum]
  have hC : ∑ m ∈ range K, fT k' ((max (la m) 0 : ℤ) : ℝ) = ∑ l ∈ range lst.length, fT k' (al l) := by
    have c1 : ∑ m ∈ range K, fT k' ((max (la m) 0 : ℤ) : ℝ) = ∑ m ∈ range K, fT k' (al m) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mem_range] at hm
      rw [hal, if_pos hm]
    have c2 : ∑ m ∈ range K, fT k' (al m) = ∑ m ∈ range (K + lst.length), fT k' (al m) := by
      apply Finset.sum_subset
      · intro m hm
        rw [Finset.mem_range] at hm ⊢
        omega
      · intro m _ hnm
        rw [Finset.mem_range] at hnm
        rw [halK m (by omega), F0]
    have c3 : ∑ m ∈ range lst.length, fT k' (al m) = ∑ m ∈ range (K + lst.length), fT k' (al m) := by
      apply Finset.sum_subset
      · intro m hm
        rw [Finset.mem_range] at hm ⊢
        omega
      · intro m _ hnm
        rw [Finset.mem_range] at hnm
        rw [halL m (by omega), F0]
    rw [c1, c2, c3]
  obtain ⟨-, P2, P3, P4⟩ := h34 k' lst.length al Bs hk hal0
    (fun l hl => by rw [hBs]; exact_mod_cast h1 l hl)
    (fun l hl => by rw [hBs, hBs]; exact_mod_cast h2 l hl)
    (fun u _ => by
      have h' : ((tailPos K la u : ℤ) : ℝ) ≤ (((lst.drop u).sum : ℕ) : ℝ) := by
        have h3u := h3 u
        generalize (lst.drop u).sum = s at h3u ⊢
        exact_mod_cast h3u
      rw [hA u, hB u] at h'
      linarith)
  refine ⟨?_, ?_⟩
  · rw [hC]
    exact le_trans P2 P3
  · intro u₀ X hX hT
    rw [hA u₀, hB u₀] at hT
    have hu : u₀ < lst.length := by
      by_contra hc
      simp only [Finset.Ico_eq_empty_of_le (show lst.length ≤ u₀ by omega), Finset.sum_empty] at hT
      linarith
    refine ⟨hu, ?_⟩
    obtain ⟨Q1, Q2⟩ := P4 u₀ X hu hX.le (by linarith)
    rw [hC]
    exact le_trans Q1 Q2

end TTyp

namespace TTyp

def revW (n : ℕ) (la : ℕ → ℤ) : ℕ → ℤ := fun m => -(la (n - 1 - m))

lemma lat_pred (q : ℕ → Bool) (B : ℕ → ℕ) {i : ℕ} (hi : 1 ≤ i) (h : q i = false) :
    lat q B (i - 1) = lat q B i := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [lat_succ, if_neg (by simp [h]), Nat.add_sub_cancel]

lemma tailPos_split (n : ℕ) (la : ℕ → ℤ) {u : ℕ} (hu : u < n) :
    tailPos n la u = max (la u) 0 + tailPos n la (u + 1) := by
  unfold tailPos
  have hs : (range n).filter (fun m => u ≤ m) = insert u ((range n).filter (fun m => u + 1 ≤ m)) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    constructor
    · intro h
      omega
    · intro h
      omega
  rw [hs, Finset.sum_insert (by simp)]

lemma drop_split (l : List ℕ) (u : ℕ) : (l.drop u).sum = l.getD u 0 + (l.drop (u + 1)).sum := list_sum_drop_eq_getD_add_sum_drop_succ l u

lemma key (h31 : LogBinomialProperties) (h34 : LogBinomialDeficit) (k' K : ℕ) (la : ℕ → ℤ) (q : ℕ → Bool) (B : ℕ → ℕ) (n0 : ℕ)
    (hk : 1 ≤ k')
    (h1 : ∀ l, l < (lat q B n0).length → k' ≤ (lat q B n0).getD l 0)
    (h2 : ∀ l, l + 1 < (lat q B n0).length → 4 * (lat q B n0).getD (l + 1) 0 ≤ (lat q B n0).getD l 0)
    (h3 : ∀ u, tailPos K la u ≤ (((lat q B n0).drop u).sum : ℕ))
    (i₀ u : ℕ) (X : ℝ) (hX : 0 < X)
    (hd : ((tailPos K la (u + ((Icc (i₀ + 1) n0).filter (fun l => q l = true)).card) : ℤ) : ℝ) ≤
      ((((lat q B n0).drop (u + ((Icc (i₀ + 1) n0).filter (fun l => q l = true)).card)).sum : ℕ) : ℝ)
        - X) :
    u < (lat q B (min i₀ n0)).length ∧
    (∑ m ∈ range K, fT k' ((max (la m) 0 : ℤ) : ℝ)) -
      (∑ l ∈ range (lat q B n0).length, fT k' (((lat q B n0).getD l 0 : ℕ) : ℝ)) ≤
        -(X * k' / (4 * (((lat q B (min i₀ n0)).getD u 0 : ℕ) : ℝ))) := by
  have hcard : ((Icc (i₀ + 1) n0).filter (fun l => q l = true)).card =
      ((Icc (min i₀ n0 + 1) n0).filter (fun l => q l = true)).card := by
    by_cases h : i₀ ≤ n0
    · rw [min_eq_left h]
    · rw [min_eq_right (by omega), Finset.Icc_eq_empty_of_lt (by omega : n0 < i₀ + 1),
        Finset.Icc_eq_empty_of_lt (by omega : n0 < n0 + 1)]
  obtain ⟨hsh1, hsh2⟩ := lat_shift q B (min_le_right i₀ n0)
  rw [hcard] at hd
  obtain ⟨hlt, hbd⟩ := (bracket h31 h34 k' K la (lat q B n0) hk h1 h2 h3).2 _ X hX hd
  rw [hsh1 u] at hbd
  exact ⟨by omega, hbd⟩

lemma a_fin {La b p k k' g : ℝ} (hLa : 0 < La) (hp : 0 < p) (hk : 0 < k) (hk' : 0 ≤ k')
    (hg0 : 0 < g) (hg : g ≤ 4 * b / p) : La * k' / (16 * k) ≤ (La * b / (p * k)) * k' / (4 * g) := by
  have hpos : 0 ≤ La * k' / (4 * k) := div_nonneg (mul_nonneg hLa.le hk') (by linarith)
  refine _root_.Formalism.InvariantFactorPaths.BranchingDimensions.le_div_of_mul_le_of_pos' (by linarith) ?_
  calc La * k' / (16 * k) * (4 * g) = La * k' / (4 * k) * g := by ring
    _ ≤ La * k' / (4 * k) * (4 * b / p) := mul_le_mul_of_nonneg_left hg hpos
    _ = La * b / (p * k) * k' := by ring

end TTyp

private theorem le_exp_mul_of_log_le_add_log {w T E : ℝ} (hw : 0 < w) (hT : 0 < T) (h : Real.log w ≤ E + Real.log T) :
    w ≤ Real.exp E * T := by
  have h' := Real.exp_le_exp.mpr h
  rwa [Real.exp_log hw, Real.exp_add, Real.exp_log hT] at h'

theorem pathWeightBound_of :
    PathEntryBounds → PathInterlacingCriterion → LogBinomialProperties → LogWeylDimensionEstimate → LogRankEstimate → PathTailBounds → LogBinomialDeficit → PathWeightBound := by
  intro h20 h21 h31 h32 h33 h35 h34 D a p La b hW hPB hTD mu hP
  have h21' := h21
  unfold LogWeylDimensionEstimate at h32
  unfold LogRankEstimate at h33
  unfold PathTailBounds at h35
  unfold PathInterlacingCriterion at h21'
  have hWF := hW
  obtain ⟨hr1, hK1, h3r, hvr, hvn⟩ := hWF
  have hPB' := hPB
  obtain ⟨ha3, hpr, hp13, hBi, hdv, hdc, -, -, h2r, hkK, hNa⟩ := hPB'
  have hk : D.k = D.r + D.K := rfl
  have hn0 : D.n0 = D.Ns - D.r := rfl
  have hk' : D.k' = D.K - 2 * D.Ns := rfl
  have hK2 : 2 * D.Ns ≤ D.K := by omega
  have hk'1 : 1 ≤ D.k' := by omega
  have hnr : D.n0 + D.r = D.Ns := by omega
  have hmin : min D.Ns D.n0 = D.n0 := min_eq_right (by omega)
  have hSL : D.stLen D.Ns = D.K := by
    unfold Formalism.InvariantFactorPaths.BranchingDimensions.Letters.stLen
    omega
  have hstage : stage mu D.Ns = Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns := by
    funext l
    simp only [Formalism.InvariantFactorPaths.BranchingDimensions.Letters.stage, Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows]
    exact congrArg (Formalism.InvariantFactorPaths.BranchingDimensions.Letters.ent mu D.Ns) (by omega)
  have hRV : ∀ i, D.latestV i = Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat (fun l => D.vec l) D.B (min i D.n0) := fun i => rfl
  have hRC : ∀ i, D.latestC i = Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat (fun l => !D.vec l) D.B (min i D.n0) := fun i => rfl
  have hP' := hP
  unfold Formalism.InvariantFactorPaths.BranchingDimensions.Letters.IsPATH at hP'
  have hdomN : ∀ m, m + 1 < D.k → Formalism.InvariantFactorPaths.BranchingDimensions.Letters.ent mu D.Ns (m + 1) ≤ Formalism.InvariantFactorPaths.BranchingDimensions.Letters.ent mu D.Ns m := hP'.2.1 D.Ns le_rfl
  have hdomK : Dom D.K (Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns) := by
    unfold Dom
    intro m hm
    show Formalism.InvariantFactorPaths.BranchingDimensions.Letters.ent mu D.Ns (D.r + (m + 1)) ≤ Formalism.InvariantFactorPaths.BranchingDimensions.Letters.ent mu D.Ns (D.r + m)
    rw [← Nat.add_assoc]
    exact hdomN (D.r + m) (by omega)
  have hposc : ((range D.K).filter fun m => 0 < Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns m).card ≤ D.Ns := by
    calc _ ≤ (range D.Ns).card := by
          apply Finset.card_le_card
          intro m hm
          simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢
          by_contra hc
          have := (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.ent_sign h20 hW hP (i := D.Ns) (m := D.r + m) le_rfl (by omega)).2 (by omega)
          have e : Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns m = Formalism.InvariantFactorPaths.BranchingDimensions.Letters.ent mu D.Ns (D.r + m) := rfl
          omega
      _ = D.Ns := Finset.card_range _
  have hnegc : ((range D.K).filter fun m => Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns m < 0).card ≤ D.Ns := by
    calc _ ≤ (Ico (D.K - D.Ns) D.K).card := by
          apply Finset.card_le_card
          intro m hm
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hm ⊢
          refine ⟨?_, hm.1⟩
          by_contra hc
          have := (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.ent_sign h20 hW hP (i := D.Ns) (m := D.r + m) le_rfl (by omega)).1 (by omega)
          have e : Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns m = Formalism.InvariantFactorPaths.BranchingDimensions.Letters.ent mu D.Ns (D.r + m) := rfl
          omega
      _ = D.Ns := by
          rw [Nat.card_Ico]
          omega
  have hC := (h21' D mu hW).2 hP
  have hlab : ∀ l, l < D.K → -(D.beNeg : ℤ) ≤ Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns l ∧ Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns l ≤ D.bePos := by
    intro l hl
    have h := hC.2.2.1 D.r le_rfl l (by omega)
    rw [hnr, hstage] at h
    exact ⟨le_trans hC.1 h.1, le_trans h.2 hC.2.1⟩
  have hbe : (D.be : ℝ) ≤ 2 * a * D.Ns := Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.be_le D (by linarith) (fun i h1 h2 => (hBi i h1 h2).2)
  have hA0 : ((max (Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns 0) 0 + max (-(Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns (D.K - 1))) 0 : ℤ) : ℝ) ≤ 2 * a * D.Ns := by
    have e := Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.be_eq D
    have h0 := hlab 0 (by omega)
    have h1 := hlab (D.K - 1) (by omega)
    have hz : max (Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns 0) 0 + max (-(Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns (D.K - 1))) 0 ≤ (D.be : ℤ) := by
      have m1 : max (Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns 0) 0 ≤ (D.bePos : ℤ) := max_le h0.2 (by positivity)
      have m2 : max (-(Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns (D.K - 1))) 0 ≤ (D.beNeg : ℤ) := max_le (by linarith [h1.1]) (by positivity)
      rw [e]
      push_cast
      linarith
    have hz' : ((max (Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns 0) 0 + max (-(Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns (D.K - 1))) 0 : ℤ) : ℝ) ≤ (D.be : ℝ) := by
      exact_mod_cast hz
    linarith
  have hLW := h32 D.r D.K D.Ns D.K (Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns) (2 * a * D.Ns) hK2 le_rfl (by omega) hdomK hposc hnegc hA0
  rw [← hk'] at hLW
  have hLR := (h33 D (2 * a) (by linarith) hr1 (by omega) hK2 (fun i h1 h2 => (hBi i h1 h2).2)).1
  have hsplitB : ∑ i ∈ Icc 1 D.n0, fT D.k' (D.B i : ℝ) =
      ∑ i ∈ (Icc 1 D.n0).filter (fun i => D.vec i = true), fT D.k' (D.B i : ℝ) +
      ∑ i ∈ (Icc 1 D.n0).filter (fun i => (!D.vec i) = true), fT D.k' (D.B i : ℝ) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Icc 1 D.n0) (fun i => D.vec i = true)]
    congr 1
    apply Finset.sum_congr _ (fun _ _ => rfl)
    apply Finset.filter_congr
    intro x _
    simp
  have hSv := Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.sum_lat (fun x : ℕ => fT D.k' (x : ℝ)) (fun l => D.vec l) D.B D.n0
  have hSc := Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.sum_lat (fun x : ℕ => fT D.k' (x : ℝ)) (fun l => !D.vec l) D.B D.n0
  have hLk : ∀ (q : ℕ → Bool) l, l < (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat q D.B D.n0).length →
      D.k' ≤ (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat q D.B D.n0).getD l 0 := by
    intro q l hl
    obtain ⟨j, hj1, hj2, -, hx⟩ := Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.mem_lat (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.getD_mem hl)
    rw [hx]
    have := (hBi j hj1 hj2).1
    omega
  have hp2 : 169 ≤ p ^ 2 := by
    calc 169 = 13 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp13 2
  have hL4v : ∀ l, l + 1 < (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat (fun l => D.vec l) D.B D.n0).length →
      4 * (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat (fun l => D.vec l) D.B D.n0).getD (l + 1) 0 ≤
        (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat (fun l => D.vec l) D.B D.n0).getD l 0 := by
    intro l hl
    have h := hdv l (by rw [hRV, min_self]; exact hl)
    rw [hRV, min_self] at h
    have h' := Nat.mul_le_mul hp2 (le_refl ((Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat (fun l => D.vec l) D.B D.n0).getD (l + 1) 0))
    linarith
  have hL4c : ∀ l, l + 1 < (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat (fun l => !D.vec l) D.B D.n0).length →
      4 * (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat (fun l => !D.vec l) D.B D.n0).getD (l + 1) 0 ≤
        (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat (fun l => !D.vec l) D.B D.n0).getD l 0 := by
    intro l hl
    have h := hdc l (by rw [hRC, min_self]; exact hl)
    rw [hRC, min_self] at h
    have h' := Nat.mul_le_mul hp2 (le_refl ((Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat (fun l => !D.vec l) D.B D.n0).getD (l + 1) 0))
    linarith
  have hTv : ∀ u, tailPos D.K (Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns) u ≤
      (((Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat (fun l => D.vec l) D.B D.n0).drop u).sum : ℕ) := by
    intro u
    have h := ((h35 D mu hW hP).1 D.Ns u le_rfl).1
    rw [hSL, hstage] at h
    unfold Formalism.InvariantFactorPaths.BranchingDimensions.Letters.SPos at h
    rw [hRV, hmin] at h
    exact h
  have hTc : ∀ u, tailPos D.K (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.revW D.K (Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns)) u ≤
      (((Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat (fun l => !D.vec l) D.B D.n0).drop u).sum : ℕ) := by
    intro u
    have h := ((h35 D mu hW hP).1 D.Ns u le_rfl).2
    rw [hSL, hstage] at h
    unfold Formalism.InvariantFactorPaths.BranchingDimensions.Letters.SNeg at h
    rw [hRC, hmin] at h
    exact h
  have hBv := Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.bracket h31 h34 D.k' D.K (Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns)
    (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat (fun l => D.vec l) D.B D.n0) hk'1 (hLk _) hL4v hTv
  have hBc := Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.bracket h31 h34 D.k' D.K (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.revW D.K (Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns))
    (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat (fun l => !D.vec l) D.B D.n0) hk'1 (hLk _) hL4c hTc
  have hrefl : ∑ m ∈ range D.K, fT D.k' ((max (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.revW D.K (Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns) m) 0 : ℤ) : ℝ) =
      ∑ m ∈ range D.K, fT D.k' ((max (-(Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns m)) 0 : ℤ) : ℝ) :=
    Finset.sum_range_reflect (fun m => fT D.k' ((max (-(Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns m)) 0 : ℤ) : ℝ)) D.K
  have hx2 : 0 ≤ 2 * a * (D.Ns : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg _)
  have hL0 : 0 ≤ Real.log (1 + 2 * a * D.Ns) := Real.log_nonneg (by linarith)
  have hcoef : (2 * (D.Ns : ℝ) * D.r + 8 * (D.Ns : ℝ) ^ 2) * Real.log (1 + 2 * a * D.Ns) ≤
      9 * (D.Ns : ℝ) ^ 2 * Real.log (1 + 2 * a * D.Ns) := by
    have h2r' : 2 * (D.r : ℝ) ≤ D.Ns := by exact_mod_cast h2r
    have hN0 : (0 : ℝ) ≤ D.Ns := Nat.cast_nonneg _
    have : 2 * (D.Ns : ℝ) * D.r + 8 * (D.Ns : ℝ) ^ 2 ≤ 9 * (D.Ns : ℝ) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hL0
  have hw : Formalism.InvariantFactorPaths.BranchingDimensions.Letters.wt mu = weylDim D.K (Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns) := rfl
  have hwpos : 0 < Formalism.InvariantFactorPaths.BranchingDimensions.Letters.wt mu := by rw [hw]; exact hLW.1
  have hTpos : (0 : ℝ) < D.rankAA := by
    have : 0 < D.rankAA := by
      unfold Formalism.InvariantFactorPaths.BranchingDimensions.Letters.rankAA
      exact Finset.prod_pos (fun i _ => Nat.choose_pos (by omega))
    exact_mod_cast this
  have hbase := hLW.2.2
  refine ⟨le_exp_mul_of_log_le_add_log hwpos hTpos (by
    rw [hw]
    linarith [hBv.1, hBc.1]), fun hnt => ?_⟩
  apply le_exp_mul_of_log_le_add_log hwpos hTpos
  rw [hw]
  unfold Formalism.InvariantFactorPaths.BranchingDimensions.Letters.Typical at hnt
  have hTD' := hTD
  obtain ⟨hLa, hTDb⟩ := hTD'
  have hkR : (0 : ℝ) < D.k := by
    have : 0 < D.k := by omega
    exact_mod_cast this
  have hpR : (0 : ℝ) < p := by
    have := hpr.pos
    exact_mod_cast this
  have hk'R : (0 : ℝ) ≤ D.k' := Nat.cast_nonneg _
  have hm1 := min_le_left (La * D.k' / (16 * D.k)) ((D.k' : ℝ) / 12)
  have hm2 := min_le_right (La * D.k' / (16 * D.k)) ((D.k' : ℝ) / 12)
  rcases not_and_or.mp hnt with hc1 | hc23
  · push_neg at hc1
    obtain ⟨i, hi1, hiN, hvi, hgt⟩ := hc1
    have hir : D.r < i := by
      by_contra h
      push_neg at h
      have := hvr i hi1 h
      simp [this] at hvi
    have hin0 : i ≤ D.n0 := by
      by_contra h
      push_neg at h
      have := hvn i h hiN
      simp [this] at hvi
    have hX : D.XT p La b i = La * b i / (p * D.k) := rfl
    have hbpos := (hTDb i hir hiN).1
    have hB4 := (hTDb i hir hiN).2
    have hXpos : 0 < D.XT p La b i := by
      rw [hX]
      exact div_pos (mul_pos hLa hbpos) (mul_pos hpR hkR)
    have t1 := ((h35 D mu hW hP).1 (i - 1) 0 (by omega)).1
    have heqv : D.SPos 0 (i - 1) = D.SPos 0 i := by
      unfold Formalism.InvariantFactorPaths.BranchingDimensions.Letters.SPos
      rw [hRV, hRV, min_eq_left (by omega : i - 1 ≤ D.n0), min_eq_left hin0,
        Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat_pred (fun l => D.vec l) D.B (i := i) (by omega) hvi]
    have hd1 : ((tailPos (D.stLen i) (stage mu i) 0 : ℤ) : ℝ) ≤ (D.SPos 0 i : ℝ) - D.XT p La b i := by
      have t1R : ((tailPos (D.stLen (i - 1)) (stage mu (i - 1)) 0 : ℤ) : ℝ) ≤ (D.SPos 0 (i - 1) : ℝ) := by
        exact_mod_cast t1
      rw [heqv] at t1R
      rw [Int.cast_sub] at hgt
      linarith
    have t2 := (h35 D mu hW hP).2.1 i 0 (D.XT p La b i) hiN hXpos.le hd1
    rw [hSL, hstage] at t2
    unfold Formalism.InvariantFactorPaths.BranchingDimensions.Letters.SPos at t2
    rw [hRV, min_self] at t2
    have td := Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.key h31 h34 D.k' D.K (Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns) (fun l => D.vec l) D.B D.n0 hk'1
      (hLk _) hL4v hTv i 0 _ hXpos t2
    obtain ⟨l, hl1, hl2, hql, hgx⟩ := Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.mem_lat (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.getD_mem td.1)
    have hli : l ≠ i := by
      rintro rfl
      simp [hql] at hvi
    have hlmin := min_le_left i D.n0
    have hlmin' := min_le_right i D.n0
    have hgle : (D.B l : ℝ) ≤ 4 * b i / p := hB4 l hl1 (by omega) (by omega)
    have hg0 : (0 : ℝ) < D.B l := by
      have := (hBi l hl1 (by omega)).1
      have : 0 < D.B l := by omega
      exact_mod_cast this
    have hthr := Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.a_fin hLa hpR hkR hk'R hg0 hgle
    have td2 := td.2
    rw [hgx, hX] at td2
    linarith [hBv.1, hBc.1]
  rcases not_and_or.mp hc23 with hc2 | hc3
  · push_neg at hc2
    obtain ⟨i, hir, hiN, hvi, hgt⟩ := hc2
    have hX : D.XT p La b i = La * b i / (p * D.k) := rfl
    have hbpos := (hTDb i hir hiN).1
    have hB4 := (hTDb i hir hiN).2
    have hXpos : 0 < D.XT p La b i := by
      rw [hX]
      exact div_pos (mul_pos hLa hbpos) (mul_pos hpR hkR)
    have t1 := ((h35 D mu hW hP).1 (i - 1) 0 (by omega)).2
    have heqc : D.SNeg 0 (i - 1) = D.SNeg 0 i := by
      unfold Formalism.InvariantFactorPaths.BranchingDimensions.Letters.SNeg
      rw [hRC, hRC]
      by_cases hin : i ≤ D.n0
      · rw [min_eq_left (by omega : i - 1 ≤ D.n0), min_eq_left hin,
          Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat_pred (fun l => !D.vec l) D.B (i := i) (by omega) (by simp [hvi])]
      · rw [min_eq_right (by omega : D.n0 ≤ i - 1), min_eq_right (by omega : D.n0 ≤ i)]
    have hd2 : ((tailNeg (D.stLen i) (stage mu i) 0 : ℤ) : ℝ) ≤ (D.SNeg 0 i : ℝ) - D.XT p La b i := by
      have t1R : ((tailNeg (D.stLen (i - 1)) (stage mu (i - 1)) 0 : ℤ) : ℝ) ≤ (D.SNeg 0 (i - 1) : ℝ) := by
        exact_mod_cast t1
      rw [heqc] at t1R
      rw [Int.cast_sub] at hgt
      linarith
    have t2 := (h35 D mu hW hP).2.2 i 0 (D.XT p La b i) hiN hXpos.le hd2
    rw [hSL, hstage] at t2
    unfold Formalism.InvariantFactorPaths.BranchingDimensions.Letters.SNeg at t2
    rw [hRC, min_self] at t2
    have hfc : ((Icc (i + 1) D.n0).filter (fun l => D.vec l = false)) =
        ((Icc (i + 1) D.n0).filter (fun l => (!D.vec l) = true)) :=
      Finset.filter_congr (fun x _ => by simp)
    rw [hfc] at t2
    have td := Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.key h31 h34 D.k' D.K (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.revW D.K (Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns))
      (fun l => !D.vec l) D.B D.n0 hk'1 (hLk _) hL4c hTc i 0 _ hXpos t2
    obtain ⟨l, hl1, hl2, hql, hgx⟩ := Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.mem_lat (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.getD_mem td.1)
    have hli : l ≠ i := by
      rintro rfl
      simp [hvi] at hql
    have hlmin := min_le_left i D.n0
    have hlmin' := min_le_right i D.n0
    have hgle : (D.B l : ℝ) ≤ 4 * b i / p := hB4 l hl1 (by omega) (by omega)
    have hg0 : (0 : ℝ) < D.B l := by
      have := (hBi l hl1 (by omega)).1
      have : 0 < D.B l := by omega
      exact_mod_cast this
    have hthr := Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.a_fin hLa hpR hkR hk'R hg0 hgle
    have td2 := td.2
    rw [hgx, hX] at td2
    linarith [hBv.1, hBc.1]
  · push_neg at hc3
    obtain ⟨i, hir, hiN, hgt⟩ := hc3
    have hh : D.Bo i =
        (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat (fun l => D.vec l) D.B (min (i - 1) D.n0)).getD (D.r - 1 - (i - 1 - D.n0)) 0 := rfl
    have hent0 : 0 ≤ Formalism.InvariantFactorPaths.BranchingDimensions.Letters.ent mu (i - 1) (D.r - 1) :=
      (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.ent_sign h20 hW hP (i := i - 1) (m := D.r - 1) (by omega) (by omega)).1 (by omega)
    have hhpos : (0 : ℝ) < D.Bo i := by
      rcases Nat.eq_zero_or_pos (D.Bo i) with h0 | h0
      · have hz : ((D.Bo i : ℕ) : ℝ) = 0 := by rw [h0]; simp
        have : (0 : ℝ) ≤ Formalism.InvariantFactorPaths.BranchingDimensions.Letters.ent mu (i - 1) (D.r - 1) := by exact_mod_cast hent0
        linarith
      · exact_mod_cast h0
    have hstu : stage mu (i - 1) (D.r - 1 - (i - 1 - D.n0)) = Formalism.InvariantFactorPaths.BranchingDimensions.Letters.ent mu (i - 1) (D.r - 1) := by
      simp only [Formalism.InvariantFactorPaths.BranchingDimensions.Letters.stage]
      exact congrArg (Formalism.InvariantFactorPaths.BranchingDimensions.Letters.ent mu (i - 1)) (by omega)
    have hus : D.r - 1 - (i - 1 - D.n0) < D.stLen (i - 1) := by
      unfold Formalism.InvariantFactorPaths.BranchingDimensions.Letters.stLen
      omega
    have hsplitT := Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.tailPos_split (D.stLen (i - 1)) (stage mu (i - 1)) hus
    rw [hstu] at hsplitT
    have t1 := ((h35 D mu hW hP).1 (i - 1) (D.r - 1 - (i - 1 - D.n0) + 1) (by omega)).1
    have hds : D.SPos (D.r - 1 - (i - 1 - D.n0)) (i - 1) =
        D.Bo i + D.SPos (D.r - 1 - (i - 1 - D.n0) + 1) (i - 1) := by
      unfold Formalism.InvariantFactorPaths.BranchingDimensions.Letters.SPos Formalism.InvariantFactorPaths.BranchingDimensions.Letters.Bo
      exact Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.drop_split _ _
    have hmx : (((max (Formalism.InvariantFactorPaths.BranchingDimensions.Letters.ent mu (i - 1) (D.r - 1)) 0 : ℤ)) : ℝ) ≤ (2 / 3) * (D.Bo i : ℝ) := by
      rw [max_eq_left hent0]
      exact hgt.le
    have hd3 : ((tailPos (D.stLen (i - 1)) (stage mu (i - 1)) (D.r - 1 - (i - 1 - D.n0)) : ℤ) : ℝ) ≤
        (D.SPos (D.r - 1 - (i - 1 - D.n0)) (i - 1) : ℝ) - (D.Bo i : ℝ) / 3 := by
      have t1R : ((tailPos (D.stLen (i - 1)) (stage mu (i - 1)) (D.r - 1 - (i - 1 - D.n0) + 1) : ℤ) : ℝ) ≤
          (D.SPos (D.r - 1 - (i - 1 - D.n0) + 1) (i - 1) : ℝ) := by
        exact_mod_cast t1
      rw [hsplitT, hds, Int.cast_add, Nat.cast_add]
      linarith
    have hX3 : (0 : ℝ) < (D.Bo i : ℝ) / 3 := by linarith
    have t2 := (h35 D mu hW hP).2.1 (i - 1) (D.r - 1 - (i - 1 - D.n0)) ((D.Bo i : ℝ) / 3) (by omega) hX3.le hd3
    rw [hSL, hstage] at t2
    unfold Formalism.InvariantFactorPaths.BranchingDimensions.Letters.SPos at t2
    rw [hRV, min_self] at t2
    have td := Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.key h31 h34 D.k' D.K (Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns) (fun l => D.vec l) D.B D.n0 hk'1
      (hLk _) hL4v hTv (i - 1) (D.r - 1 - (i - 1 - D.n0)) _ hX3 t2
    have td2 := td.2
    rw [← hh] at td2
    have hne : (D.Bo i : ℝ) ≠ 0 := ne_of_gt hhpos
    have e12 : (D.Bo i : ℝ) / 3 * D.k' / (4 * D.Bo i) = D.k' / 12 := by
      field_simp
      ring
    rw [e12] at td2
    linarith [hBv.1, hBc.1]

end Formalism.InvariantFactorPaths.BranchingDimensions
