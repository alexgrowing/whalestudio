import Formalism.ThetaLogCoordinates.ResidueClassEstimates.StatementT

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.BranchingDimensions

open Letters

lemma sum_filter_Icc_succ (p : ℕ → Prop) [DecidablePred p] (f : ℕ → ℕ) (a i : ℕ) (h : a ≤ i + 1) :
    ∑ l ∈ (Icc a (i + 1)).filter p, f l =
      (∑ l ∈ (Icc a i).filter p, f l) + if p (i + 1) then f (i + 1) else 0 := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_Icc_succ_top h]

lemma card_filter_Icc_succ (p : ℕ → Prop) [DecidablePred p] (a i : ℕ) (h : a ≤ i + 1) :
    ((Icc a (i + 1)).filter p).card = ((Icc a i).filter p).card + if p (i + 1) then 1 else 0 := by
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_Icc_succ_top h]

lemma Dom.anti {n : ℕ} {la : ℕ → ℤ} (h : Dom n la) : ∀ a b, a ≤ b → b < n → la b ≤ la a := by
  intro a b hab hb
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih => exact (h b hb).trans (ih (by omega))

lemma HStrip.diff_le {n : ℕ} {a b : ℕ → ℤ} (h : HStrip n a b) (m : ℕ) (hm : m < n) :
    b m - a m ≤ wsize n b - wsize n a := by
  unfold wsize
  rw [← Finset.sum_sub_distrib]
  exact Finset.single_le_sum (f := fun j => b j - a j)
    (fun j hj => sub_nonneg.mpr (h.1 j (Finset.mem_range.mp hj))) (Finset.mem_range.mpr hm)

def revW (n : ℕ) (la : ℕ → ℤ) : ℕ → ℤ := fun m => -(la (n - 1 - m))

lemma tailNeg_eq (n : ℕ) (la : ℕ → ℤ) (u : ℕ) : tailNeg n la u = tailPos n (revW n la) u := rfl

lemma HStrip.rev {n : ℕ} {a b : ℕ → ℤ} (h : HStrip n a b) : HStrip n (revW n b) (revW n a) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun m hm => ?_, fun m hm => ?_⟩
  · simp only [revW]
    exact neg_le_neg (h1 _ (by omega))
  · simp only [revW]
    have h3 := h2 (n - 1 - (m + 1)) (by omega)
    have e : n - 1 - (m + 1) + 1 = n - 1 - m := by omega
    rw [e] at h3
    exact neg_le_neg h3

lemma Interl.rev {n : ℕ} {a b : ℕ → ℤ} (h : Interl n a b) : Interl n (revW n a) (revW (n + 1) b) := by
  intro l hl
  have h3 := h (n - 1 - l) (by omega)
  simp only [revW]
  have e1 : n + 1 - 1 - l = n - 1 - l + 1 := by omega
  have e2 : n + 1 - 1 - (l + 1) = n - 1 - l := by omega
  rw [e1, e2]
  exact ⟨neg_le_neg h3.2, neg_le_neg h3.1⟩

lemma wsize_rev (n : ℕ) (la : ℕ → ℤ) : wsize n (revW n la) = - wsize n la := by
  unfold wsize revW
  rw [Finset.sum_neg_distrib]
  have h := Finset.sum_range_reflect (fun m => la m) n
  try simp only at h
  rw [h]

lemma tailPos_succ (n : ℕ) (la : ℕ → ℤ) (u : ℕ) :
    tailPos (n + 1) la u = tailPos n la u + if u ≤ n then max (la n) 0 else 0 := by
  unfold tailPos
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_range_succ]

lemma tailPos_le_succ (n : ℕ) (la : ℕ → ℤ) (u : ℕ) : tailPos n la u ≤ tailPos (n + 1) la u := by
  rw [tailPos_succ]
  split_ifs
  · linarith [le_max_right (la n) 0]
  · linarith

lemma tailPos_mono {n : ℕ} {a b : ℕ → ℤ} (h : ∀ m, m < n → a m ≤ b m) (u : ℕ) :
    tailPos n a u ≤ tailPos n b u := by
  unfold tailPos
  apply Finset.sum_le_sum
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_range] at hm
  exact max_le_max (h m hm.1) le_rfl

lemma tail_pos_shift_le (a b : ℕ → ℤ) (u : ℕ) :
    ∀ n, (∀ m, m + 1 < n + 1 → b (m + 1) ≤ a m) → tailPos (n + 1) b (u + 1) ≤ tailPos n a u := by
  intro n
  induction n with
  | zero =>
    intro _
    simp [tailPos, Finset.filter_singleton]
  | succ n ih =>
    intro h
    rw [tailPos_succ (n + 1) b, tailPos_succ n a]
    have h1 := ih (fun m hm => h m (by omega))
    have h2 : b (n + 1) ≤ a n := h n (by omega)
    have h3 : max (b (n + 1)) 0 ≤ max (a n) 0 := max_le_max h2 le_rfl
    have hiff : (u + 1 ≤ n + 1) ↔ (u ≤ n) := by omega
    simp only [hiff]
    split_ifs <;> linarith

lemma HStrip.tailPos_shift {n : ℕ} {a b : ℕ → ℤ} (h : HStrip n a b) (u : ℕ) :
    tailPos n b (u + 1) ≤ tailPos n a u := by
  cases n with
  | zero => simp [tailPos]
  | succ k =>
    exact (tail_pos_shift_le a b u k (fun m hm => h.2 m hm)).trans (tailPos_le_succ k a u)

lemma HStrip.tailPos_le {n : ℕ} {a b : ℕ → ℤ} (h : HStrip n a b) (u : ℕ) :
    tailPos n a u ≤ tailPos n b u := tailPos_mono h.1 u

lemma wsize_eq_tails (n : ℕ) (a : ℕ → ℤ) : wsize n a = tailPos n a 0 - tailPos n (revW n a) 0 := by
  unfold wsize tailPos revW
  rw [Finset.sum_filter, Finset.sum_filter]
  simp only [Nat.zero_le, if_true, ite_true]
  have h := Finset.sum_range_reflect (fun m => max (-(a m)) 0) n
  try simp only at h
  rw [h, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rcases le_total 0 (a m) with h0 | h0
  · rw [max_eq_left h0, max_eq_right (by linarith)]
    ring
  · rw [max_eq_right h0, max_eq_left (by linarith)]
    ring

lemma HStrip.tailPos_zero {n : ℕ} {a b : ℕ → ℤ} (h : HStrip n a b) :
    tailPos n b 0 - tailPos n a 0 ≤ wsize n b - wsize n a := by
  rw [wsize_eq_tails n b, wsize_eq_tails n a]
  have h1 := HStrip.tailPos_le h.rev 0
  linarith

lemma Interl.tailPos_le {n : ℕ} {a b : ℕ → ℤ} (h : Interl n a b) (u : ℕ) :
    tailPos n a u ≤ tailPos (n + 1) b u :=
  (tailPos_mono (fun m hm => (h m hm).1) u).trans (tailPos_le_succ n b u)

lemma Interl.size {n : ℕ} {a b : ℕ → ℤ} (h : Interl n a b) :
    b n ≤ wsize (n + 1) b - wsize n a ∧ wsize (n + 1) b - wsize n a ≤ b 0 := by
  constructor
  · unfold wsize
    rw [Finset.sum_range_succ]
    have h1 : ∑ m ∈ range n, a m ≤ ∑ m ∈ range n, b m :=
      Finset.sum_le_sum fun m hm => (h m (Finset.mem_range.mp hm)).1
    linarith
  · unfold wsize
    rw [Finset.sum_range_succ']
    have h1 : ∑ m ∈ range n, b (m + 1) ≤ ∑ m ∈ range n, a m :=
      Finset.sum_le_sum fun m hm => (h m (Finset.mem_range.mp hm)).2
    linarith

lemma latest_succ (q : ℕ → Bool) (B : ℕ → ℕ) (i : ℕ) :
    (((List.range' 1 (i + 1)).filter q).reverse).map B =
      if q (i + 1) = true then B (i + 1) :: (((List.range' 1 i).filter q).reverse).map B
      else (((List.range' 1 i).filter q).reverse).map B := by
  by_cases hq : q (i + 1) = true
  · simp [List.range'_concat, List.filter_append, hq, add_comm]
  · simp [List.range'_concat, List.filter_append, hq, add_comm]

lemma abs_bound (N : ℕ) (T : ℕ → ℕ → ℤ) (S : ℕ → ℕ → ℕ) (act : ℕ → Bool)
    (h0 : ∀ u, T 0 u ≤ S u 0)
    (hA : ∀ i u, i < N → act (i + 1) = true → T (i + 1) (u + 1) ≤ T i u ∧ S (u + 1) (i + 1) = S u i)
    (hA0 : ∀ i, i < N → act (i + 1) = true → T (i + 1) 0 - T i 0 ≤ (S 0 (i + 1) : ℤ) - S 0 i)
    (hI : ∀ i u, i < N → act (i + 1) = false → T (i + 1) u ≤ T i u ∧ S u (i + 1) = S u i) :
    ∀ i, i ≤ N → ∀ u, T i u ≤ S u i := by
  intro i
  induction i with
  | zero =>
    intro _ u
    exact h0 u
  | succ i ih =>
    intro hi u
    have ih' := ih (by omega)
    by_cases ha : act (i + 1) = true
    · cases u with
      | zero =>
        have h1 := hA0 i (by omega) ha
        have h2 := ih' 0
        linarith
      | succ u =>
        obtain ⟨h1, h2⟩ := hA i u (by omega) ha
        rw [h2]
        exact h1.trans (ih' u)
    · have ha' : act (i + 1) = false := by simpa using ha
      obtain ⟨h1, h2⟩ := hI i u (by omega) ha'
      rw [h2]
      exact h1.trans (ih' u)

lemma deficit_persists_of_active_inactive_recursion (N : ℕ) (T : ℕ → ℕ → ℤ) (S : ℕ → ℕ → ℕ) (act : ℕ → Bool)
    (hA : ∀ i u, i < N → act (i + 1) = true → T (i + 1) (u + 1) ≤ T i u ∧ S (u + 1) (i + 1) = S u i)
    (hI : ∀ i u, i < N → act (i + 1) = false → T (i + 1) u ≤ T i u ∧ S u (i + 1) = S u i)
    (i₀ u : ℕ) (X : ℝ) (h : ((T i₀ u : ℤ) : ℝ) ≤ (S u i₀ : ℝ) - X) :
    ∀ i, i₀ ≤ i → i ≤ N →
      ((T i (u + ((Icc (i₀ + 1) i).filter fun l => act l = true).card) : ℤ) : ℝ) ≤
        (S (u + ((Icc (i₀ + 1) i).filter fun l => act l = true).card) i : ℝ) - X := by
  intro i hi hiN
  induction i, hi using Nat.le_induction with
  | base =>
    have hc : ((Icc (i₀ + 1) i₀).filter fun l => act l = true).card = 0 := by simp
    rw [hc, add_zero]
    exact h
  | succ i hi ih =>
    have ih' := ih (by omega)
    rw [card_filter_Icc_succ _ (i₀ + 1) i (by omega)]
    generalize hc : ((Icc (i₀ + 1) i).filter fun l => act l = true).card = c at ih' ⊢
    split_ifs with ha
    · obtain ⟨h1, h2⟩ := hA i (u + c) (by omega) ha
      rw [← add_assoc, h2]
      have h1' : ((T (i + 1) (u + c + 1) : ℤ) : ℝ) ≤ ((T i (u + c) : ℤ) : ℝ) := by exact_mod_cast h1
      linarith
    · rw [add_zero]
      have ha' : act (i + 1) = false := by simpa using ha
      obtain ⟨h1, h2⟩ := hI i (u + c) (by omega) ha'
      rw [h2]
      have h1' : ((T (i + 1) (u + c) : ℤ) : ℝ) ≤ ((T i (u + c) : ℤ) : ℝ) := by exact_mod_cast h1
      linarith

variable {D : Letters} {mu : D.Stages}

lemma n0_le_Ns (D : Letters) : D.n0 ≤ D.Ns := Nat.sub_le _ _

lemma Ns_eq (hW : D.Wf) : D.Ns = D.n0 + D.r := by
  obtain ⟨_, _, h3, _⟩ := hW
  unfold Letters.n0
  omega

lemma r_lt_k (hW : D.Wf) : D.r < D.k := by
  have h := hW.2.1
  unfold Letters.k
  omega

lemma stage_le (i : ℕ) (h : i ≤ D.n0) : stage mu i = ent mu i := by
  funext l
  simp [Letters.stage, Nat.sub_eq_zero_of_le h]

lemma stage_add (j l : ℕ) : stage mu (D.n0 + j) l = ent mu (D.n0 + j) (l + j) := by
  simp [Letters.stage]

lemma stLen_le (i : ℕ) (h : i ≤ D.n0) : D.stLen i = D.k := by
  unfold Letters.stLen
  rw [Nat.sub_eq_zero_of_le h, Nat.sub_zero]

lemma stLen_add (j : ℕ) : D.stLen (D.n0 + j) = D.k - j := by
  unfold Letters.stLen
  rw [Nat.add_sub_cancel_left]

lemma pre_of_path (h : D.IsPATH mu) : D.IsPre mu := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := h
  exact ⟨h1, fun i hi => h2 i (hi.trans (n0_le_Ns D)),
    fun i hi1 hi2 hv => h3 i hi1 (hi2.trans (n0_le_Ns D)) hv,
    fun i hi1 hi2 hv => h4 i hi1 (hi2.trans (n0_le_Ns D)) hv, h5, h6⟩

lemma be_eq (D : Letters) : D.be = D.bePos + D.beNeg := by
  unfold Letters.be Letters.bePos Letters.beNeg
  rw [← Finset.sum_filter_add_sum_filter_not (Icc 1 D.n0) (fun i => D.vec i = true)]
  congr 2
  ext i
  simp

lemma pre_size (hk : 1 ≤ D.k) (hP : D.IsPre mu) : ∀ i, i ≤ D.n0 →
    -((∑ l ∈ (Icc 1 i).filter (fun l => D.vec l = false), D.B l : ℕ) : ℤ) ≤ ent mu i (D.k - 1) ∧
    ent mu i 0 ≤ ((∑ l ∈ (Icc 1 i).filter (fun l => D.vec l = true), D.B l : ℕ) : ℤ) := by
  intro i
  induction i with
  | zero =>
    intro _
    simp [hP.1]
  | succ i ih =>
    intro hi
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    rw [sum_filter_Icc_succ _ _ _ _ (by omega), sum_filter_Icc_succ _ _ _ _ (by omega)]
    have hk1 : D.k - 1 < D.k := by omega
    have hk0 : 0 < D.k := by omega
    by_cases hv : D.vec (i + 1) = true
    · have hS := hP.2.2.1 (i + 1) (by omega) hi hv
      have hW := hP.2.2.2.2.1 (i + 1) (by omega) hi hv
      simp only [Nat.add_sub_cancel] at hS hW
      have hd := HStrip.diff_le hS 0 hk0
      have h1 := hS.1 (D.k - 1) hk1
      rw [if_neg (by simp [hv]), if_pos hv]
      push_cast at ih1 ih2 ⊢
      constructor <;> linarith
    · have hv' : D.vec (i + 1) = false := by simpa using hv
      have hS := hP.2.2.2.1 (i + 1) (by omega) hi hv'
      have hW := hP.2.2.2.2.2 (i + 1) (by omega) hi hv'
      simp only [Nat.add_sub_cancel] at hS hW
      have hd := HStrip.diff_le hS (D.k - 1) hk1
      have h1 := hS.1 0 hk0
      rw [if_pos hv', if_neg hv]
      push_cast at ih1 ih2 ⊢
      constructor <;> linarith

lemma path_rows (hP : D.IsPATH mu) : ∀ i, i ≤ D.Ns →
    (∀ m, D.nVec i ≤ m → m < D.k → ent mu i m ≤ 0) ∧ ∀ m, m + D.nCov i < D.k → 0 ≤ ent mu i m := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨fun m _ _ => ?_, fun m _ => ?_⟩ <;> simp [hP.1]
  | succ i ih =>
    intro hi
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    simp only [Letters.nVec, Letters.nCov] at ih1 ih2 ⊢
    rw [card_filter_Icc_succ _ _ _ (by omega), card_filter_Icc_succ _ _ _ (by omega)]
    by_cases hv : D.vec (i + 1) = true
    · have hS := hP.2.2.1 (i + 1) (by omega) hi hv
      simp only [Nat.add_sub_cancel] at hS
      rw [if_pos hv, if_neg (by simp [hv])]
      refine ⟨fun m hm hmk => ?_, fun m hm => ?_⟩
      · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        exact (hS.2 m' hmk).trans (ih1 m' (by omega) (by omega))
      · exact (ih2 m (by omega)).trans (hS.1 m (by omega))
    · have hv' : D.vec (i + 1) = false := by simpa using hv
      have hS := hP.2.2.2.1 (i + 1) (by omega) hi hv'
      simp only [Nat.add_sub_cancel] at hS
      rw [if_neg hv, if_pos hv']
      refine ⟨fun m hm hmk => ?_, fun m hm => ?_⟩
      · exact (hS.1 m hmk).trans (ih1 m (by omega) hmk)
      · exact (ih2 (m + 1) (by omega)).trans (hS.2 m (by omega))

theorem pathEntryBounds : PathEntryBounds := by
  intro D mu hW hP
  have hk : 1 ≤ D.k := by
    have := hW.1
    unfold Letters.k
    omega
  exact ⟨pre_size hk (pre_of_path hP), path_rows hP⟩

lemma interl_of_path (hW : D.Wf) (hP : D.IsPATH mu) (j : ℕ) (hj : j < D.r) :
    Interl (D.k - (j + 1)) (stage mu (D.n0 + (j + 1))) (stage mu (D.n0 + j)) := by
  intro l hl
  have hNs := Ns_eq hW
  have hv : D.vec (D.n0 + (j + 1)) = true := hW.2.2.2.2 _ (by omega) (by omega)
  have hS := hP.2.2.1 (D.n0 + (j + 1)) (by omega) (by omega) hv
  have e1 : D.n0 + (j + 1) - 1 = D.n0 + j := by omega
  rw [e1] at hS
  simp only [stage_add]
  constructor
  · rw [show l + (j + 1) = l + j + 1 by omega]
    exact hS.2 (l + j) (by omega)
  · rw [show l + 1 + j = l + (j + 1) by omega]
    exact hS.1 (l + (j + 1)) (by omega)

lemma tails_range (hD : Dom D.k (ent mu D.n0))
    (hI : ∀ j, j < D.r → Interl (D.k - (j + 1)) (stage mu (D.n0 + (j + 1))) (stage mu (D.n0 + j))) :
    ∀ j, j ≤ D.r → ∀ l, l < D.k - j →
      ent mu D.n0 (D.k - 1) ≤ stage mu (D.n0 + j) l ∧ stage mu (D.n0 + j) l ≤ ent mu D.n0 0 := by
  intro j
  induction j with
  | zero =>
    intro _ l hl
    rw [stage_add]
    simp only [Nat.add_zero] at hl ⊢
    exact ⟨hD.anti l (D.k - 1) (by omega) (by omega), hD.anti 0 l (Nat.zero_le _) (by omega)⟩
  | succ j ih =>
    intro hj l hl
    obtain ⟨h1, h2⟩ := hI j (by omega) l (by omega)
    obtain ⟨h3, h4⟩ := ih (by omega) l (by omega)
    obtain ⟨h5, h6⟩ := ih (by omega) (l + 1) (by omega)
    exact ⟨h5.trans h2, h1.trans h4⟩

lemma path_of_interl (hW : D.Wf) (hPre : D.IsPre mu)
    (hH : ∀ i', 1 ≤ i' → i' ≤ D.r → ∀ m, m < i' → ent mu (D.n0 + i') m = D.be)
    (hI : ∀ j, j < D.r → Interl (D.k - (j + 1)) (stage mu (D.n0 + (j + 1))) (stage mu (D.n0 + j))) :
    D.IsPATH mu := by
  have hNs := Ns_eq hW
  have hrk := r_lt_k hW
  have hk1 : 1 ≤ D.k := by omega
  have hD0 : Dom D.k (ent mu D.n0) := hPre.2.1 D.n0 le_rfl
  have hTR := tails_range hD0 hI
  have hn0be : ent mu D.n0 0 ≤ (D.be : ℤ) := by
    have h := (pre_size hk1 hPre D.n0 le_rfl).2
    have hb : (∑ l ∈ (Icc 1 D.n0).filter (fun l => D.vec l = true), D.B l) ≤ D.be := by
      rw [be_eq]
      unfold Letters.bePos
      omega
    exact h.trans (by exact_mod_cast hb)
  have hcur : ∀ j, j ≤ D.r → ∀ m, j ≤ m → ent mu (D.n0 + j) m = stage mu (D.n0 + j) (m - j) := by
    intro j _ m hm
    rw [stage_add, Nat.sub_add_cancel hm]
  have hDom : ∀ i, i ≤ D.Ns → Dom D.k (ent mu i) := by
    intro i hi
    by_cases hin : i ≤ D.n0
    · exact hPre.2.1 i hin
    obtain ⟨j, rfl⟩ : ∃ j, i = D.n0 + j := ⟨i - D.n0, by omega⟩
    have hjr : j ≤ D.r := by omega
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hIj := hI j' (by omega)
    intro m hm
    rcases lt_trichotomy (m + 1) (j' + 1) with h | h | h
    · rw [hH _ (by omega) hjr m (by omega), hH _ (by omega) hjr (m + 1) h]
    · have hm' : m = j' := by omega
      rw [hm', hH _ (by omega) hjr j' (by omega), hcur (j' + 1) hjr (j' + 1) le_rfl, Nat.sub_self]
      exact ((hTR (j' + 1) hjr 0 (by omega)).2).trans hn0be
    · rw [hcur _ hjr (m + 1) (by omega), hcur _ hjr m (by omega)]
      have hl : m + 1 - (j' + 1) = m - (j' + 1) + 1 := by omega
      rw [hl]
      exact (hIj (m - (j' + 1) + 1) (by omega)).1.trans (hIj (m - (j' + 1)) (by omega)).2
  refine ⟨hPre.1, hDom, ?_, ?_, hPre.2.2.2.2.1, hPre.2.2.2.2.2, hH⟩
  · intro i h1 hi hv
    by_cases hin : i ≤ D.n0
    · exact hPre.2.2.1 i h1 hin hv
    obtain ⟨j, rfl⟩ : ∃ j, i = D.n0 + j := ⟨i - D.n0, by omega⟩
    have hjr : j ≤ D.r := by omega
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hIj := hI j' (by omega)
    rw [show D.n0 + (j' + 1) - 1 = D.n0 + j' by omega]
    refine ⟨fun m hm => ?_, fun m hm => ?_⟩
    · rcases lt_trichotomy m j' with h | h | h
      · rw [hH j' (by omega) (by omega) m h, hH (j' + 1) (by omega) hjr m (by omega)]
      · rw [h, hH (j' + 1) (by omega) hjr j' (by omega), hcur j' (by omega) j' le_rfl, Nat.sub_self]
        exact ((hTR j' (by omega) 0 (by omega)).2).trans hn0be
      · rw [hcur j' (by omega) m (by omega), hcur (j' + 1) hjr m (by omega)]
        have hl : m - j' = m - (j' + 1) + 1 := by omega
        rw [hl]
        exact (hIj (m - (j' + 1)) (by omega)).2
    · by_cases h : m < j'
      · rw [hH (j' + 1) (by omega) hjr (m + 1) (by omega), hH j' (by omega) (by omega) m h]
      · rw [hcur (j' + 1) hjr (m + 1) (by omega), hcur j' (by omega) m (by omega)]
        have hl : m + 1 - (j' + 1) = m - j' := by omega
        rw [hl]
        exact (hIj (m - j') (by omega)).1
  · intro i h1 hi hv
    by_cases hin : i ≤ D.n0
    · exact hPre.2.2.2.1 i h1 hin hv
    · have h' := hW.2.2.2.2 i (by omega) hi
      simp [h'] at hv

lemma wsize_head (j : ℕ) (hj : j ≤ D.k) (hH : ∀ m, m < j → ent mu (D.n0 + j) m = D.be) :
    wsize D.k (ent mu (D.n0 + j)) = (j : ℤ) * D.be + wsize (D.k - j) (stage mu (D.n0 + j)) := by
  unfold wsize
  have hk : D.k = j + (D.k - j) := by omega
  conv_lhs => rw [hk]
  rw [Finset.sum_range_add, Finset.sum_congr rfl (fun m hm => hH m (Finset.mem_range.1 hm)),
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [stage_add, Nat.add_comm m j]

theorem pathInterlacingCriterion : PathInterlacingCriterion := by
  intro D mu hW
  have hNs := Ns_eq hW
  have hrk := r_lt_k hW
  have hk1 : 1 ≤ D.k := by omega
  have hr1 : 1 ≤ D.r := hW.1
  refine ⟨fun hPre hH => ⟨fun hP i' h1 h2 => ?_, fun h => ?_⟩, fun hP => ?_⟩
  · have hIj := interl_of_path hW hP (i' - 1) (by omega)
    rw [show i' - 1 + 1 = i' by omega, show D.n0 + (i' - 1) = D.n0 + i' - 1 by omega] at hIj
    exact hIj
  · refine path_of_interl hW hPre hH (fun j hj => ?_)
    have hIj := h (j + 1) (by omega) (by omega)
    rw [show D.n0 + (j + 1) - 1 = D.n0 + j by omega] at hIj
    exact hIj
  · have hpre : -(D.beNeg : ℤ) ≤ ent mu D.n0 (D.k - 1) ∧ ent mu D.n0 0 ≤ (D.bePos : ℤ) :=
      pre_size hk1 (pre_of_path hP) D.n0 le_rfl
    have hD0 : Dom D.k (ent mu D.n0) := hP.2.1 D.n0 (n0_le_Ns D)
    have hTR := tails_range hD0 (fun j hj => interl_of_path hW hP j hj)
    have hbe : (D.be : ℤ) = D.bePos + D.beNeg := by exact_mod_cast be_eq D
    refine ⟨hpre.1, hpre.2, hTR, fun i' h1 h2 => ?_⟩
    have hH' : ∀ m, m < i' → ent mu (D.n0 + i') m = D.be := hP.2.2.2.2.2.2 i' h1 h2
    have hHm : ∀ m, m < i' - 1 → ent mu (D.n0 + (i' - 1)) m = D.be :=
      fun m hm => hP.2.2.2.2.2.2 (i' - 1) (by omega) (by omega) m hm
    have e1 := wsize_head i' (by omega) hH'
    have e2 := wsize_head (i' - 1) (by omega) hHm
    have hIj := interl_of_path hW hP (i' - 1) (by omega)
    rw [show i' - 1 + 1 = i' by omega] at hIj
    have hsz := hIj.size
    rw [show D.k - i' + 1 = D.k - (i' - 1) by omega] at hsz
    have hT0 := hTR (i' - 1) (by omega) 0 (by omega)
    have hT1 := hTR (i' - 1) (by omega) (D.k - i') (by omega)
    rw [show D.n0 + i' - 1 = D.n0 + (i' - 1) by omega, e1, e2]
    have hc : ((i' - 1 : ℕ) : ℤ) = (i' : ℤ) - 1 := by omega
    rw [hc]
    refine ⟨by ring, ?_, ?_⟩ <;> linarith [hsz.1, hsz.2, hT0.2, hT1.1, hpre.1, hpre.2]

lemma latestV_succ (i : ℕ) (hi : i + 1 ≤ D.n0) :
    D.latestV (i + 1) = if D.vec (i + 1) = true then D.B (i + 1) :: D.latestV i else D.latestV i := by
  unfold Letters.latestV
  rw [min_eq_left hi, min_eq_left (by omega)]
  exact latest_succ D.vec D.B i

lemma latestC_succ (i : ℕ) (hi : i + 1 ≤ D.n0) :
    D.latestC (i + 1) = if (!D.vec (i + 1)) = true then D.B (i + 1) :: D.latestC i else D.latestC i := by
  unfold Letters.latestC
  rw [min_eq_left hi, min_eq_left (by omega)]
  exact latest_succ (fun l => !D.vec l) D.B i

lemma latestV_frame (i j : ℕ) (hi : D.n0 ≤ i) (hj : D.n0 ≤ j) : D.latestV i = D.latestV j := by
  unfold Letters.latestV
  rw [min_eq_right hi, min_eq_right hj]

lemma latestC_frame (i j : ℕ) (hi : D.n0 ≤ i) (hj : D.n0 ≤ j) : D.latestC i = D.latestC j := by
  unfold Letters.latestC
  rw [min_eq_right hi, min_eq_right hj]

lemma tailPos_of_zero {n : ℕ} {a : ℕ → ℤ} (h : ∀ m, a m = 0) (u : ℕ) : tailPos n a u = 0 := by
  simp [tailPos, h]

def actV (D : Letters) (l : ℕ) : Bool := decide (l ≤ D.n0) && D.vec l

def actC (D : Letters) (l : ℕ) : Bool := decide (l ≤ D.n0) && !D.vec l

lemma actV_true {l : ℕ} : actV D l = true ↔ l ≤ D.n0 ∧ D.vec l = true := by
  simp [actV]

lemma actC_true {l : ℕ} : actC D l = true ↔ l ≤ D.n0 ∧ D.vec l = false := by
  simp [actC]

lemma card_actV (i₀ : ℕ) : ((Icc (i₀ + 1) D.Ns).filter fun l => actV D l = true).card =
    ((Icc (i₀ + 1) D.n0).filter fun l => D.vec l = true).card := by
  have hn := n0_le_Ns D
  congr 1
  ext l
  simp only [Finset.mem_filter, Finset.mem_Icc, actV_true]
  constructor
  · rintro ⟨⟨h1, _⟩, h3, h4⟩
    exact ⟨⟨h1, h3⟩, h4⟩
  · rintro ⟨⟨h1, h2⟩, h4⟩
    exact ⟨⟨h1, le_trans h2 hn⟩, h2, h4⟩

lemma card_actC (i₀ : ℕ) : ((Icc (i₀ + 1) D.Ns).filter fun l => actC D l = true).card =
    ((Icc (i₀ + 1) D.n0).filter fun l => D.vec l = false).card := by
  have hn := n0_le_Ns D
  congr 1
  ext l
  simp only [Finset.mem_filter, Finset.mem_Icc, actC_true]
  constructor
  · rintro ⟨⟨h1, _⟩, h3, h4⟩
    exact ⟨⟨h1, h3⟩, h4⟩
  · rintro ⟨⟨h1, h2⟩, h4⟩
    exact ⟨⟨h1, le_trans h2 hn⟩, h2, h4⟩

lemma frame_step (hW : D.Wf) (hP : D.IsPATH mu) (i u : ℕ) (hi : i < D.Ns) (hn : D.n0 ≤ i) :
    tailPos (D.stLen (i + 1)) (stage mu (i + 1)) u ≤ tailPos (D.stLen i) (stage mu i) u ∧
    tailNeg (D.stLen (i + 1)) (stage mu (i + 1)) u ≤ tailNeg (D.stLen i) (stage mu i) u := by
  obtain ⟨j, rfl⟩ : ∃ j, i = D.n0 + j := ⟨i - D.n0, by omega⟩
  have hNs := Ns_eq hW
  have hj : j < D.r := by omega
  have hI := interl_of_path hW hP j hj
  have hl1 : D.stLen (D.n0 + j + 1) = D.k - (j + 1) := by rw [add_assoc, stLen_add]
  have hl0 : D.stLen (D.n0 + j) = D.k - j := stLen_add j
  have hkj : D.k - j = D.k - (j + 1) + 1 := by
    have := r_lt_k hW
    omega
  rw [hl1, hl0, hkj, show D.n0 + j + 1 = D.n0 + (j + 1) by ring]
  refine ⟨hI.tailPos_le u, ?_⟩
  rw [tailNeg_eq, tailNeg_eq]
  exact hI.rev.tailPos_le u

lemma vec_step (hP : D.IsPATH mu) (i : ℕ) (hi : i + 1 ≤ D.n0) (hv : D.vec (i + 1) = true) :
    HStrip D.k (ent mu i) (ent mu (i + 1)) ∧
      wsize D.k (ent mu (i + 1)) - wsize D.k (ent mu i) = D.B (i + 1) := by
  obtain ⟨-, -, h3, -, h5, -, -⟩ := hP
  have e : i + 1 - 1 = i := by omega
  have ha := h3 (i + 1) (by omega) (hi.trans (n0_le_Ns D)) hv
  have hb := h5 (i + 1) (by omega) hi hv
  rw [e] at ha hb
  exact ⟨ha, hb⟩

lemma cov_step (hP : D.IsPATH mu) (i : ℕ) (hi : i + 1 ≤ D.n0) (hv : D.vec (i + 1) = false) :
    HStrip D.k (ent mu (i + 1)) (ent mu i) ∧
      wsize D.k (ent mu i) - wsize D.k (ent mu (i + 1)) = D.B (i + 1) := by
  obtain ⟨-, -, -, h4, -, h6, -⟩ := hP
  have e : i + 1 - 1 = i := by omega
  have ha := h4 (i + 1) (by omega) (hi.trans (n0_le_Ns D)) hv
  have hb := h6 (i + 1) (by omega) hi hv
  rw [e] at ha hb
  exact ⟨ha, hb⟩

lemma pos_A (hP : D.IsPATH mu) (i u : ℕ) (ha : actV D (i + 1) = true) :
    tailPos (D.stLen (i + 1)) (stage mu (i + 1)) (u + 1) ≤ tailPos (D.stLen i) (stage mu i) u ∧
      D.SPos (u + 1) (i + 1) = D.SPos u i := by
  obtain ⟨hi, hv⟩ := actV_true.1 ha
  have hS := hP.2.2.1 (i + 1) (by omega) (hi.trans (n0_le_Ns D)) hv
  simp only [Nat.add_sub_cancel] at hS
  refine ⟨?_, ?_⟩
  · rw [stLen_le _ hi, stLen_le _ (by omega), stage_le _ hi, stage_le _ (by omega)]
    exact hS.tailPos_shift u
  · unfold Letters.SPos
    rw [latestV_succ i hi, if_pos hv, List.drop_succ_cons]

lemma pos_active_zero (hP : D.IsPATH mu) (i : ℕ) (ha : actV D (i + 1) = true) :
    tailPos (D.stLen (i + 1)) (stage mu (i + 1)) 0 - tailPos (D.stLen i) (stage mu i) 0 ≤
      (D.SPos 0 (i + 1) : ℤ) - D.SPos 0 i := by
  obtain ⟨hi, hv⟩ := actV_true.1 ha
  have hS := hP.2.2.1 (i + 1) (by omega) (hi.trans (n0_le_Ns D)) hv
  have hW := hP.2.2.2.2.1 (i + 1) (by omega) hi hv
  simp only [Nat.add_sub_cancel] at hS hW
  rw [stLen_le _ hi, stLen_le _ (by omega), stage_le _ hi, stage_le _ (by omega)]
  unfold Letters.SPos
  rw [latestV_succ i hi, if_pos hv, List.drop_zero, List.drop_zero, List.sum_cons]
  have h1 := hS.tailPos_zero
  push_cast
  linarith

lemma pos_I (hW : D.Wf) (hP : D.IsPATH mu) (i u : ℕ) (hN : i < D.Ns) (ha : actV D (i + 1) = false) :
    tailPos (D.stLen (i + 1)) (stage mu (i + 1)) u ≤ tailPos (D.stLen i) (stage mu i) u ∧
      D.SPos u (i + 1) = D.SPos u i := by
  by_cases hi : i + 1 ≤ D.n0
  · have hv : D.vec (i + 1) = false := by
      by_contra h
      have h' : actV D (i + 1) = true := actV_true.2 ⟨hi, by simpa using h⟩
      simp [h'] at ha
    have hS := hP.2.2.2.1 (i + 1) (by omega) (hi.trans (n0_le_Ns D)) hv
    simp only [Nat.add_sub_cancel] at hS
    refine ⟨?_, ?_⟩
    · rw [stLen_le _ hi, stLen_le _ (by omega), stage_le _ hi, stage_le _ (by omega)]
      exact tailPos_mono hS.1 u
    · unfold Letters.SPos
      rw [latestV_succ i hi, if_neg (by simp [hv])]
  · refine ⟨(frame_step hW hP i u hN (by omega)).1, ?_⟩
    unfold Letters.SPos
    rw [latestV_frame (i + 1) i (by omega) (by omega)]

lemma neg_A (hP : D.IsPATH mu) (i u : ℕ) (ha : actC D (i + 1) = true) :
    tailNeg (D.stLen (i + 1)) (stage mu (i + 1)) (u + 1) ≤ tailNeg (D.stLen i) (stage mu i) u ∧
      D.SNeg (u + 1) (i + 1) = D.SNeg u i := by
  obtain ⟨hi, hv⟩ := actC_true.1 ha
  have hS := hP.2.2.2.1 (i + 1) (by omega) (hi.trans (n0_le_Ns D)) hv
  simp only [Nat.add_sub_cancel] at hS
  refine ⟨?_, ?_⟩
  · rw [stLen_le _ hi, stLen_le _ (by omega), stage_le _ hi, stage_le _ (by omega), tailNeg_eq, tailNeg_eq]
    exact hS.rev.tailPos_shift u
  · unfold Letters.SNeg
    rw [latestC_succ i hi, if_pos (by simp [hv]), List.drop_succ_cons]

lemma neg_active_zero (hP : D.IsPATH mu) (i : ℕ) (ha : actC D (i + 1) = true) :
    tailNeg (D.stLen (i + 1)) (stage mu (i + 1)) 0 - tailNeg (D.stLen i) (stage mu i) 0 ≤
      (D.SNeg 0 (i + 1) : ℤ) - D.SNeg 0 i := by
  obtain ⟨hi, hv⟩ := actC_true.1 ha
  have hS := hP.2.2.2.1 (i + 1) (by omega) (hi.trans (n0_le_Ns D)) hv
  have hW := hP.2.2.2.2.2.1 (i + 1) (by omega) hi hv
  simp only [Nat.add_sub_cancel] at hS hW
  rw [stLen_le _ hi, stLen_le _ (by omega), stage_le _ hi, stage_le _ (by omega), tailNeg_eq, tailNeg_eq]
  unfold Letters.SNeg
  rw [latestC_succ i hi, if_pos (by simp [hv]), List.drop_zero, List.drop_zero, List.sum_cons]
  have h1 := hS.rev.tailPos_zero
  rw [wsize_rev, wsize_rev] at h1
  push_cast
  linarith

lemma neg_I (hW : D.Wf) (hP : D.IsPATH mu) (i u : ℕ) (hN : i < D.Ns) (ha : actC D (i + 1) = false) :
    tailNeg (D.stLen (i + 1)) (stage mu (i + 1)) u ≤ tailNeg (D.stLen i) (stage mu i) u ∧
      D.SNeg u (i + 1) = D.SNeg u i := by
  by_cases hi : i + 1 ≤ D.n0
  · have hv : D.vec (i + 1) = true := by
      by_contra h
      have h' : actC D (i + 1) = true := actC_true.2 ⟨hi, by simpa using h⟩
      simp [h'] at ha
    have hS := hP.2.2.1 (i + 1) (by omega) (hi.trans (n0_le_Ns D)) hv
    simp only [Nat.add_sub_cancel] at hS
    refine ⟨?_, ?_⟩
    · rw [stLen_le _ hi, stLen_le _ (by omega), stage_le _ hi, stage_le _ (by omega), tailNeg_eq, tailNeg_eq]
      exact tailPos_mono (fun m hm => by unfold revW; exact neg_le_neg (hS.1 _ (by omega))) u
    · unfold Letters.SNeg
      rw [latestC_succ i hi, if_neg (by simp [hv])]
  · refine ⟨(frame_step hW hP i u hN (by omega)).2, ?_⟩
    unfold Letters.SNeg
    rw [latestC_frame (i + 1) i (by omega) (by omega)]

theorem pathTailBounds : PathTailBounds := by
  intro D mu hW hP
  have hk0 : ∀ u, tailPos (D.stLen 0) (stage mu 0) u = 0 := by
    intro u
    apply tailPos_of_zero
    intro m
    rw [stage_le 0 (Nat.zero_le _)]
    exact hP.1 m
  have hk0' : ∀ u, tailNeg (D.stLen 0) (stage mu 0) u = 0 := by
    intro u
    rw [tailNeg_eq]
    apply tailPos_of_zero
    intro m
    simp [revW, stage_le 0 (Nat.zero_le _), hP.1]
  have bP := abs_bound D.Ns (fun i u => tailPos (D.stLen i) (stage mu i) u) (fun u i => D.SPos u i) (actV D)
    (fun u => by
      show tailPos (D.stLen 0) (stage mu 0) u ≤ (D.SPos u 0 : ℤ)
      rw [hk0]
      exact Nat.cast_nonneg _)
    (fun i u _ ha => pos_A hP i u ha) (fun i _ ha => pos_active_zero hP i ha) (fun i u hi ha => pos_I hW hP i u hi ha)
  have bN := abs_bound D.Ns (fun i u => tailNeg (D.stLen i) (stage mu i) u) (fun u i => D.SNeg u i) (actC D)
    (fun u => by
      show tailNeg (D.stLen 0) (stage mu 0) u ≤ (D.SNeg u 0 : ℤ)
      rw [hk0']
      exact Nat.cast_nonneg _)
    (fun i u _ ha => neg_A hP i u ha) (fun i _ ha => neg_active_zero hP i ha) (fun i u hi ha => neg_I hW hP i u hi ha)
  have hsP : ∀ v, D.SPos v D.Ns = D.SPos v D.n0 := fun v => by
    unfold Letters.SPos
    rw [latestV_frame D.Ns D.n0 (n0_le_Ns D) le_rfl]
  have hsN : ∀ v, D.SNeg v D.Ns = D.SNeg v D.n0 := fun v => by
    unfold Letters.SNeg
    rw [latestC_frame D.Ns D.n0 (n0_le_Ns D) le_rfl]
  refine ⟨fun i u hi => ⟨bP i hi u, bN i hi u⟩, fun i₀ u X hi₀ _ h => ?_, fun i₀ u X hi₀ _ h => ?_⟩
  · have h1 := deficit_persists_of_active_inactive_recursion D.Ns (fun i u => tailPos (D.stLen i) (stage mu i) u) (fun u i => D.SPos u i) (actV D)
      (fun i u _ ha => pos_A hP i u ha) (fun i u hi ha => pos_I hW hP i u hi ha) i₀ u X h D.Ns hi₀ le_rfl
    beta_reduce at h1
    rw [card_actV, hsP] at h1
    exact h1
  · have h1 := deficit_persists_of_active_inactive_recursion D.Ns (fun i u => tailNeg (D.stLen i) (stage mu i) u) (fun u i => D.SNeg u i) (actC D)
      (fun i u _ ha => neg_A hP i u ha) (fun i u hi ha => neg_I hW hP i u hi ha) i₀ u X h D.Ns hi₀ le_rfl
    beta_reduce at h1
    rw [card_actC, hsN] at h1
    exact h1

end Formalism.InvariantFactorPaths.BranchingDimensions
