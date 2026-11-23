import Formalism.QuotientMetricDivisors.TheoremDivIneqRows
import Formalism.LogFactorialIndices.SignedSubspaceIndex.SumInterlacedBoundFails
import Formalism.LogFactorialIndices.SubspaceIndexSigned
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.TheoremDivIneq

open Finset

noncomputable section

namespace Formalism.DivisionValues

open Formalism.LatticeIndexTer (ph)

namespace W8

lemma log_nat_le {A : ℝ} (r : ℕ) (hA : 1 ≤ Real.log A) (hr : (r : ℝ) ≤ A) :
    Real.log (r : ℝ) ≤ Real.log A := by
  rcases Nat.eq_zero_or_pos r with h0 | h0
  · subst h0
    simp only [Nat.cast_zero, Real.log_zero]
    linarith
  · exact Real.log_le_log (by exact_mod_cast h0) hr

lemma ph_nat_le {La : ℝ} (r : ℕ) (h : Real.log (r : ℝ) ≤ La) : ph (r : ℝ) ≤ (r : ℝ) * La := by
  show (r : ℝ) * Real.log r - r ≤ r * La
  have h0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have h1 := mul_le_mul_of_nonneg_left h h0
  linarith

private lemma ph_sub_ph_le_mul_log {u v : ℝ} (hu : 0 < u) (hv : 0 ≤ v) :
    ph u - ph v ≤ (u - v) * Real.log u := by
  show u * Real.log u - u - (v * Real.log v - v) ≤ (u - v) * Real.log u
  have key : v * (Real.log u - Real.log v) ≤ u - v := by
    rcases hv.lt_or_eq with hv' | hv'
    · have hne : v ≠ 0 := hv'.ne'
      have h1 := Real.log_le_sub_one_of_pos (div_pos hu hv')
      rw [Real.log_div hu.ne' hne] at h1
      have h2 := mul_le_mul_of_nonneg_left h1 hv
      have h3 : v * (u / v) = u := by
        rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hne, mul_one]
      have h4 : v * (u / v - 1) = v * (u / v) - v := by ring
      linarith
    · subst hv'
      simp only [zero_mul, sub_zero]
      exact hu.le
  linarith

lemma ph_nat_lt (y y' : ℕ) (h : y < y') : ph (y : ℝ) - ph (y' : ℝ) ≤ 1 := by
  have hlt : (y : ℝ) < y' := by exact_mod_cast h
  have hy'pos : (0 : ℝ) < y' := lt_of_le_of_lt (Nat.cast_nonneg y) hlt
  rcases Nat.eq_zero_or_pos y with h0 | h0
  · subst h0
    have hne : (y' : ℝ) ≠ 0 := hy'pos.ne'
    have hl := Real.one_sub_inv_le_log_of_pos hy'pos
    have e : (y' : ℝ) * (1 - (y' : ℝ)⁻¹) = y' - 1 := by
      rw [mul_sub, mul_one, mul_inv_cancel₀ hne]
    have h2 := mul_le_mul_of_nonneg_left hl hy'pos.le
    simp only [ph, Nat.cast_zero, Real.log_zero, mul_zero, sub_zero, zero_sub]
    linarith
  · have hu : (0 : ℝ) < y := by exact_mod_cast h0
    have ht := ph_sub_ph_le_mul_log hu (Nat.cast_nonneg (α := ℝ) y')
    have hlog0 : 0 ≤ Real.log (y : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr h0)
    have h3 : ((y : ℝ) - y') * Real.log y ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hlog0
    linarith

lemma pair_one {La d : ℝ} (y y' : ℕ) (hy : Real.log (y : ℝ) ≤ La) (hLa : 1 ≤ La) (hd0 : 0 ≤ d)
    (hd : (y : ℝ) - (y' : ℝ) ≤ d) : ph (y : ℝ) - ph (y' : ℝ) ≤ d * La + 1 := by
  have hLa0 : 0 ≤ La := by linarith
  have hdL : 0 ≤ d * La := mul_nonneg hd0 hLa0
  rcases lt_or_ge y y' with hlt | hle
  · have := ph_nat_lt y y' hlt
    linarith
  · rcases Nat.eq_zero_or_pos y with h0 | h0
    · have hyy : y = y' := by omega
      rw [hyy, sub_self]
      linarith
    · have hu : (0 : ℝ) < y := by exact_mod_cast h0
      have ht := ph_sub_ph_le_mul_log hu (Nat.cast_nonneg (α := ℝ) y')
      have hlog0 : 0 ≤ Real.log (y : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr h0)
      have h1 : ((y : ℝ) - y') * Real.log y ≤ d * Real.log y := mul_le_mul_of_nonneg_right hd hlog0
      have h2 : d * Real.log y ≤ d * La := mul_le_mul_of_nonneg_left hy hd0
      linarith

lemma pair_abs {La d : ℝ} (y y' : ℕ) (hy : Real.log (y : ℝ) ≤ La) (hLa : 1 ≤ La)
    (hd : |(y : ℝ) - (y' : ℝ)| ≤ d) : ph (y : ℝ) - ph (y' : ℝ) ≤ d * La := by
  have hd0 : 0 ≤ d := le_trans (abs_nonneg _) hd
  rcases Nat.eq_zero_or_pos y with h0 | h0
  · subst h0
    have hy'0 : (0 : ℝ) ≤ y' := Nat.cast_nonneg _
    have hlog : 0 ≤ Real.log (y' : ℝ) := by
      rcases Nat.eq_zero_or_pos y' with h1 | h1
      · rw [h1, Nat.cast_zero, Real.log_zero]
      · exact Real.log_nonneg (Nat.one_le_cast.mpr h1)
    have habs : |((0 : ℕ) : ℝ) - (y' : ℝ)| = y' := by
      rw [Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg hy'0]
    have h2 := mul_nonneg hy'0 hlog
    have h3 := mul_le_mul_of_nonneg_left hLa hd0
    simp only [ph, Nat.cast_zero, Real.log_zero, mul_zero, sub_zero, zero_sub]
    linarith
  · have hu : (0 : ℝ) < y := by exact_mod_cast h0
    have ht := ph_sub_ph_le_mul_log hu (Nat.cast_nonneg (α := ℝ) y')
    have hlog0 : 0 ≤ Real.log (y : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr h0)
    have h1 : ((y : ℝ) - y') ≤ d := le_trans (le_abs_self _) hd
    have h2 : ((y : ℝ) - y') * Real.log y ≤ d * Real.log y := mul_le_mul_of_nonneg_right h1 hlog0
    have h3 : d * Real.log y ≤ d * La := mul_le_mul_of_nonneg_left hy hd0
    linarith

lemma phRows_add (s t : Multiset ℕ) : phRows (s + t) = phRows s + phRows t := by
  unfold phRows
  rw [Multiset.map_add, Multiset.sum_add]

lemma phRows_cons (a : ℕ) (s : Multiset ℕ) : phRows (a ::ₘ s) = ph (a : ℝ) + phRows s := by
  unfold phRows
  rw [Multiset.map_cons, Multiset.sum_cons]

lemma phRows_univ {n : ℕ} (g : Fin n → ℕ) :
    phRows (Finset.univ.val.map g) = ∑ i, ph (g i : ℝ) := by
  unfold phRows
  rw [Multiset.map_map]
  rfl

lemma logFactRows_add (s t : Multiset ℕ) :
    logFactRows (s + t) = logFactRows s + logFactRows t := by
  unfold logFactRows
  rw [Multiset.map_add, Multiset.sum_add]

lemma logFactRows_univ {n : ℕ} (g : Fin n → ℕ) :
    logFactRows (Finset.univ.val.map g) = ∑ i, Real.log ((g i).factorial : ℝ) := by
  unfold logFactRows
  rw [Multiset.map_map]
  rfl

lemma logFactRows_nonneg (s : Multiset ℕ) : 0 ≤ logFactRows s := by
  unfold logFactRows
  apply Multiset.sum_nonneg
  intro x hx
  rw [Multiset.mem_map] at hx
  obtain ⟨r, -, rfl⟩ := hx
  exact Real.log_nonneg (Nat.one_le_cast.mpr (Nat.factorial_pos r))

private lemma ph_natCast_le_log_factorial (n : ℕ) : ph (n : ℝ) ≤ Real.log (n.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    simp [ph]
  · have hn : (0 : ℝ) < n := by exact_mod_cast h0
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have h1 := Real.pow_div_factorial_le_exp (n : ℝ) hn.le n
    have h2 : Real.log ((n : ℝ) ^ n / n.factorial) ≤ n := by
      have := Real.log_le_log (div_pos (pow_pos hn n) hf) h1
      rwa [Real.log_exp] at this
    rw [Real.log_div (pow_pos hn n).ne' hf.ne', Real.log_pow] at h2
    show (n : ℝ) * Real.log n - n ≤ Real.log (n.factorial : ℝ)
    linarith

lemma sum_ph_le_logFact {n : ℕ} (r : Fin n → ℕ) (sm : Multiset ℕ) :
    ∑ i, ph (r i : ℝ) ≤ logFactRows (Finset.univ.val.map r + sm) := by
  rw [logFactRows_add, logFactRows_univ]
  have h0 := logFactRows_nonneg sm
  have h : ∑ i, ph (r i : ℝ) ≤ ∑ i, Real.log ((r i).factorial : ℝ) :=
    Finset.sum_le_sum fun i _ => ph_natCast_le_log_factorial (r i)
  linarith

lemma phRows_blk {A Bl : ℝ} (blk : Multiset ℕ) (hA : 1 ≤ Real.log A) (hb : (blk.sum : ℝ) ≤ Bl)
    (hBl : Bl ≤ A) : phRows blk ≤ Bl * Real.log A := by
  have hL0 : 0 ≤ Real.log A := by linarith
  have hmem : ∀ r ∈ blk, (r : ℝ) ≤ A := by
    intro r hr
    have h1 : r ≤ blk.sum := Multiset.le_sum_of_mem hr
    have h2 : (r : ℝ) ≤ blk.sum := by exact_mod_cast h1
    linarith
  have hsum : ∀ s : Multiset ℕ, (∀ r ∈ s, (r : ℝ) ≤ A) →
      phRows s ≤ (s.sum : ℝ) * Real.log A := by
    intro s
    refine Multiset.induction_on s ?_ ?_
    · intro _
      simp [phRows]
    · intro a s ih hs
      rw [phRows_cons, Multiset.sum_cons, Nat.cast_add]
      have ha := ph_nat_le a (log_nat_le a hA (hs a (Multiset.mem_cons.mpr (Or.inl rfl))))
      have hs' := ih (fun r hr => hs r (Multiset.mem_cons.mpr (Or.inr hr)))
      linarith
  have h1 := hsum blk hmem
  have h2 := mul_le_mul_of_nonneg_right hb hL0
  linarith

lemma sum_univ_cast {n : ℕ} (g : Fin n → ℕ) :
    (((Finset.univ.val.map g).sum : ℕ) : ℝ) = ∑ i, (g i : ℝ) := by
  have h : (Finset.univ.val.map g).sum = ∑ i, g i := rfl
  rw [h, Nat.cast_sum]

private lemma sum_castSucc_sub_succ_eq_sub_last {n : ℕ} (c : Fin (n + 1) → ℝ) :
    ∑ i : Fin n, (c i.castSucc - c i.succ) = c 0 - c (Fin.last n) := by
  induction n with
  | zero => simp
  | succ m ih =>
    have h : ∑ i : Fin m, (c i.castSucc.castSucc - c i.succ.castSucc) =
        c (0 : Fin (m + 1)).castSucc - c (Fin.last m).castSucc := ih (fun j => c j.castSucc)
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.succ_castSucc]
    rw [h]
    simp only [Fin.castSucc_zero, Fin.succ_last]
    ring

lemma telescope {n : ℕ} {c : Fin (n + 1) → ℝ} {c' : Fin n → ℝ} {S : ℝ}
    (h : Formalism.LatticeIndexTer.Interlaced n c c' S) : ∑ i : Fin n, (c i.castSucc - c' i) ≤ S := by
  have hsum : ∑ i : Fin n, (c i.castSucc - c' i) ≤ ∑ i : Fin n, (c i.castSucc - c i.succ) :=
    Finset.sum_le_sum fun i _ => by linarith [(h.2 i).2]
  rw [sum_castSucc_sub_succ_eq_sub_last] at hsum
  linarith [(h.1 0).2, (h.1 (Fin.last n)).1]

lemma telescope' {n : ℕ} {c : Fin (n + 1) → ℝ} {c' : Fin n → ℝ} {S : ℝ}
    (h : Formalism.LatticeIndexTer.Interlaced n c c' S) : ∑ i : Fin n, (c' i - c i.succ) ≤ S := by
  have hsum : ∑ i : Fin n, (c' i - c i.succ) ≤ ∑ i : Fin n, (c i.castSucc - c i.succ) :=
    Finset.sum_le_sum fun i _ => by linarith [(h.2 i).1]
  rw [sum_castSucc_sub_succ_eq_sub_last] at hsum
  linarith [(h.1 0).2, (h.1 (Fin.last n)).1]

end W8

open W8

private lemma neg_ph_natCast_le_one (r : ℕ) : -ph (r : ℝ) ≤ 1 := by
  have h0 : ph ((0 : ℕ) : ℝ) = 0 := by simp [ph]
  rcases Nat.eq_zero_or_pos r with hr | hr
  · rw [hr, h0]
    norm_num
  · have := ph_nat_lt 0 r hr
    linarith

private lemma ph_add_ph_sub_add_phRows_le_ph_add_log_mul {aT w r0 rz : ℕ} {A Bl : ℝ} {blk : Multiset ℕ}
    (hA : 1 ≤ Real.log A) (haT : (aT : ℝ) + w ≤ A) (hr0 : r0 ≤ w) (hwA : (w : ℝ) ≤ A)
    (hblk : (blk.sum : ℝ) ≤ Bl) (hBl : Bl ≤ A) :
    ph ((aT + w : ℕ) : ℝ) + ph (r0 : ℝ) - ph (rz : ℝ) + phRows blk ≤
      ph (aT : ℝ) + ((2 * (w : ℝ) + Bl) * Real.log A + 1) := by
  have hL0 : 0 ≤ Real.log A := by linarith
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg w
  have hd : |((aT + w : ℕ) : ℝ) - (aT : ℝ)| ≤ (w : ℝ) := by
    rw [abs_le]
    push_cast
    constructor <;> linarith
  have h1 := pair_abs (aT + w) aT (log_nat_le _ hA (by push_cast; linarith)) hA hd
  have hr0' : (r0 : ℝ) ≤ w := by exact_mod_cast hr0
  have h2 : ph (r0 : ℝ) ≤ (r0 : ℝ) * Real.log A := ph_nat_le r0 (log_nat_le r0 hA (by linarith))
  have h3 : (r0 : ℝ) * Real.log A ≤ (w : ℝ) * Real.log A := mul_le_mul_of_nonneg_right hr0' hL0
  have h4 := neg_ph_natCast_le_one rz
  have h5 := phRows_blk blk hA hblk hBl
  linarith

theorem young_diagram_factorial : RowsFactorial := by
  intro n w S Bl sh A La fa ν ap hLaA hLa hwS hBl hfa
  subst hLaA
  have hL0 : 0 ≤ Real.log A := by linarith
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg w
  refine ⟨fun hoff => ?_, fun aT haT htop => ?_⟩
  · obtain ⟨c, c', r, blk, sm, hI, hr, hblk, hν, hap⟩ := hoff
    subst hν
    subst hap
    have hcS : ∀ i, (c i : ℝ) ≤ S := fun i => (hI.1 i).2
    have hcA : ∀ i, ((w + c i : ℕ) : ℝ) ≤ A := fun i => by
      push_cast
      linarith [hcS i]
    have hν : phRows ((Finset.univ.val.map fun i => w + c i) + blk) =
        ∑ i : Fin n, ph ((w + c i.castSucc : ℕ) : ℝ) + ph ((w + c (Fin.last n) : ℕ) : ℝ) +
          phRows blk := by
      rw [phRows_add, phRows_univ, Fin.sum_univ_castSucc]
    have hfa' : ∑ i : Fin n, ph ((r i : ℕ) : ℝ) ≤ fa := le_trans (sum_ph_le_logFact r sm) hfa
    have hpair : ∀ i : Fin n, ph ((w + c i.castSucc : ℕ) : ℝ) - ph ((r i : ℕ) : ℝ) ≤
        ((c i.castSucc : ℝ) - c' i) * Real.log A + sh * Real.log A := by
      intro i
      obtain ⟨h1a, h1b⟩ := abs_le.mp (hr i)
      have h2 : (c' i : ℝ) ≤ c i.castSucc := (hI.2 i).1
      have hd : |((w + c i.castSucc : ℕ) : ℝ) - ((r i : ℕ) : ℝ)| ≤
          ((c i.castSucc : ℝ) - c' i) + sh := by
        rw [abs_le]
        push_cast
        constructor <;> linarith
      have := pair_abs (w + c i.castSucc) (r i) (log_nat_le _ hLa (hcA _)) hLa hd
      linarith
    have hsum : ∑ i : Fin n, ph ((w + c i.castSucc : ℕ) : ℝ) - ∑ i : Fin n, ph ((r i : ℕ) : ℝ) ≤
        (∑ i : Fin n, ((c i.castSucc : ℝ) - c' i)) * Real.log A + (n : ℝ) * (sh * Real.log A) := by
      rw [← Finset.sum_sub_distrib]
      refine le_trans (Finset.sum_le_sum fun i _ => hpair i) (le_of_eq ?_)
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    have htel : ∑ i : Fin n, ((c i.castSucc : ℝ) - c' i) ≤ S := telescope hI
    have hmul := mul_le_mul_of_nonneg_right htel hL0
    have hlast : ph ((w + c (Fin.last n) : ℕ) : ℝ) ≤ ((w : ℝ) + S) * Real.log A := by
      refine le_trans (ph_nat_le _ (log_nat_le _ hLa (hcA _))) ?_
      refine mul_le_mul_of_nonneg_right ?_ hL0
      push_cast
      linarith [hcS (Fin.last n)]
    have hb := phRows_blk blk hLa hblk hBl
    linarith
  · obtain ⟨c, c', r, r0, blk, sm, hI, hr, hr0, hblk, hν, hap⟩ := htop
    subst hν
    subst hap
    have hS0 : 0 ≤ S := le_trans (hI.1 0).1 (hI.1 0).2
    have hcS : ∀ i : Fin n, (c i : ℝ) ≤ S := fun i => le_trans (hI.2 i).1 (hI.1 i.castSucc).2
    have hcA : ∀ i : Fin n, ((w + c i : ℕ) : ℝ) ≤ A := fun i => by
      push_cast
      linarith [hcS i]
    have hν : phRows ((aT + w) ::ₘ r0 ::ₘ ((Finset.univ.val.map fun i => w + c i) + blk)) =
        ph ((aT + w : ℕ) : ℝ) + ph ((r0 : ℕ) : ℝ) + ∑ i : Fin n, ph ((w + c i : ℕ) : ℝ) +
          phRows blk := by
      rw [phRows_cons, phRows_cons, phRows_add, phRows_univ]
      ring
    have hfa' : ∑ i : Fin (n + 1), ph ((r i : ℕ) : ℝ) ≤ fa := le_trans (sum_ph_le_logFact r sm) hfa
    have hfa2 : ∑ i : Fin (n + 1), ph ((r i : ℕ) : ℝ) =
        ph ((r 0 : ℕ) : ℝ) + ∑ i : Fin n, ph ((r i.succ : ℕ) : ℝ) := Fin.sum_univ_succ _
    have hpair : ∀ i : Fin n, ph ((w + c i : ℕ) : ℝ) - ph ((r i.succ : ℕ) : ℝ) ≤
        ((c i : ℝ) - c' i.succ) * Real.log A + sh * Real.log A := by
      intro i
      obtain ⟨h1a, h1b⟩ := abs_le.mp (hr i.succ)
      have h2 : (c' i.succ : ℝ) ≤ c i := (hI.2 i).2
      have hd : |((w + c i : ℕ) : ℝ) - ((r i.succ : ℕ) : ℝ)| ≤ ((c i : ℝ) - c' i.succ) + sh := by
        rw [abs_le]
        push_cast
        constructor <;> linarith
      have := pair_abs (w + c i) (r i.succ) (log_nat_le _ hLa (hcA _)) hLa hd
      linarith
    have hsum : ∑ i : Fin n, ph ((w + c i : ℕ) : ℝ) - ∑ i : Fin n, ph ((r i.succ : ℕ) : ℝ) ≤
        (∑ i : Fin n, ((c i : ℝ) - c' i.succ)) * Real.log A + (n : ℝ) * (sh * Real.log A) := by
      rw [← Finset.sum_sub_distrib]
      refine le_trans (Finset.sum_le_sum fun i _ => hpair i) (le_of_eq ?_)
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    have htel : ∑ i : Fin n, ((c i : ℝ) - c' i.succ) ≤ S := telescope' hI
    have hmul := mul_le_mul_of_nonneg_right htel hL0
    have hrest := ph_add_ph_sub_add_phRows_le_ph_add_log_mul (rz := r 0) hLa haT hr0 (by linarith) hblk hBl
    linarith

private lemma cast_sum_map_add_offset_eq {n w : ℕ} (c : Fin (n + 1) → ℕ) (blk : Multiset ℕ) :
    ((((Finset.univ.val.map fun i => w + c i) + blk).sum : ℕ) : ℝ) =
      ((n : ℝ) + 1) * w + ∑ i, (c i : ℝ) + (blk.sum : ℝ) := by
  rw [Multiset.sum_add, Nat.cast_add, sum_univ_cast]
  simp only [Nat.cast_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_one]

private lemma cast_sum_cons_cons_map_add_offset_eq {n aT w r0 : ℕ} (c : Fin n → ℕ) (blk : Multiset ℕ) :
    ((((aT + w) ::ₘ r0 ::ₘ ((Finset.univ.val.map fun i => w + c i) + blk)).sum : ℕ) : ℝ) =
      (aT : ℝ) + ((n : ℝ) + 1) * w + r0 + ∑ i, (c i : ℝ) + (blk.sum : ℝ) := by
  rw [Multiset.sum_cons, Multiset.sum_cons, Multiset.sum_add]
  simp only [Nat.cast_add]
  rw [sum_univ_cast]
  simp only [Nat.cast_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

theorem young_diagram_period : RowsPeriod := by
  intro n w S Bl sh ν ap
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg w
  refine ⟨fun hoff => ?_, fun aT htop => ?_⟩
  · obtain ⟨c, c', r, blk, sm, hI, -, hblk, hν, -⟩ := hoff
    subst hν
    have hs := cast_sum_map_add_offset_eq (w := w) c blk
    have hcS : ∑ i, (c i : ℝ) ≤ ((n : ℝ) + 1) * S := by
      have h := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin (n + 1)))) =>
        (hI.1 i).2
      simpa using h
    have hc0 : 0 ≤ ∑ i, (c i : ℝ) := Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
    have hb0 : (0 : ℝ) ≤ blk.sum := Nat.cast_nonneg _
    constructor <;> linarith
  · obtain ⟨c, c', r, r0, blk, sm, hI, -, hr0, hblk, hν, -⟩ := htop
    subst hν
    have hs := cast_sum_cons_cons_map_add_offset_eq (aT := aT) (w := w) (r0 := r0) c blk
    have hcS : ∑ i, (c i : ℝ) ≤ (n : ℝ) * S := by
      have h := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
        le_trans (hI.2 i).1 (hI.1 i.castSucc).2
      simpa using h
    have hc0 : 0 ≤ ∑ i, (c i : ℝ) := Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
    have hb0 : (0 : ℝ) ≤ blk.sum := Nat.cast_nonneg _
    have hr0' : (r0 : ℝ) ≤ w := by exact_mod_cast hr0
    have hr00 : (0 : ℝ) ≤ r0 := Nat.cast_nonneg _
    constructor <;> linarith

private lemma prod_range_sub_eq_factorial' (n : ℕ) : ∏ j ∈ Finset.range n, (n - j) = n.factorial := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ', Nat.factorial_succ]
    have h : ∀ j ∈ Finset.range k, k + 1 - (j + 1) = k - j := fun j _ => by omega
    rw [Finset.prod_congr rfl h, ih, Nat.sub_zero]
    ring

theorem young_diagram_hook : RowsHook := by
  intro μ
  have hcell : ∀ p : ℕ × ℕ, p ∈ μ.cells ↔
      p.1 ∈ Finset.range (μ.colLen 0) ∧ p.2 ∈ Finset.range (μ.rowLen p.1) := by
    rintro ⟨i, j⟩
    simp only [YoungDiagram.mem_cells, Finset.mem_range]
    constructor
    · intro h
      exact ⟨YoungDiagram.mem_iff_lt_colLen.mp (μ.up_left_mem le_rfl (Nat.zero_le j) h),
        YoungDiagram.mem_iff_lt_rowLen.mp h⟩
    · intro h
      exact YoungDiagram.mem_iff_lt_rowLen.mpr h.2
  have hle : ∏ x ∈ μ.cells, (μ.rowLen x.1 - x.2) ≤ Formalism.LatticeIndexTer.hookProd μ := by
    unfold Formalism.LatticeIndexTer.hookProd
    apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
    rintro ⟨i, j⟩ h
    have h1 : i < μ.colLen j := YoungDiagram.mem_iff_lt_colLen.mp h
    show μ.rowLen i - j ≤ μ.rowLen i - j + (μ.colLen j - i) - 1
    omega
  have heq : ∏ x ∈ μ.cells, (μ.rowLen x.1 - x.2) =
      ∏ i ∈ Finset.range (μ.colLen 0), (μ.rowLen i).factorial := by
    rw [Finset.prod_finset_product μ.cells (Finset.range (μ.colLen 0))
      (fun i => Finset.range (μ.rowLen i)) hcell]
    exact Finset.prod_congr rfl fun i _ => prod_range_sub_eq_factorial' (μ.rowLen i)
  have hpos : 0 < ∏ i ∈ Finset.range (μ.colLen 0), (μ.rowLen i).factorial :=
    Finset.prod_pos fun i _ => Nat.factorial_pos _
  have hlog : logFactRows (μ.rowLens : Multiset ℕ) =
      ∑ i ∈ Finset.range (μ.colLen 0), Real.log ((μ.rowLen i).factorial : ℝ) := by
    unfold logFactRows YoungDiagram.rowLens
    rw [Multiset.map_coe, List.map_map]
    rfl
  rw [hlog, ← Real.log_prod (s := Finset.range (μ.colLen 0))
    (f := fun i => ((μ.rowLen i).factorial : ℝ))
    (fun i _ => (Nat.cast_pos.mpr (Nat.factorial_pos _)).ne'),
    ← Nat.cast_prod]
  apply Real.log_le_log (by exact_mod_cast hpos)
  exact_mod_cast heq.symm.le.trans hle

namespace W8

lemma arith_nN {n k N cs : ℝ} (hn : 0 ≤ n) (hnk : n ≤ k) (hkN : k ≤ N) (hcs : 0 ≤ cs) :
    n * (cs * N) ≤ cs * N ^ 2 := by
  have hN : 0 ≤ N := by linarith
  have h1 := mul_le_mul_of_nonneg_right (hnk.trans hkN) (mul_nonneg hcs hN)
  linarith

lemma arith_fact_top {w S Sc N Bl cs C0 La n k : ℝ} (hw : 0 ≤ w) (hSc0 : 0 ≤ Sc) (hBl : 0 ≤ Bl)
    (hn : 0 ≤ n) (hk : k = n + 2) (hkN : k ≤ N) (hcs : 0 ≤ cs) (hC2 : 2 ≤ C0) (hCcs : cs + 1 ≤ C0)
    (hSc : 2 * Sc ≤ C0 * S) (hLa : 1 ≤ La) :
    (2 * w + Sc + n * (cs * N) + Bl) * La + 1 ≤ C0 * (w + S + N ^ 2 + Bl) * La := by
  have hN : 2 ≤ N := by linarith
  have hnN := arith_nN hn (by linarith : n ≤ k) hkN hcs
  have hN2 : 1 ≤ N ^ 2 := by nlinarith
  have h1 := mul_le_mul_of_nonneg_right hC2 hw
  have h2 := mul_le_mul_of_nonneg_right hCcs (sq_nonneg N)
  have h3 := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ C0) hBl
  have hin : 2 * w + Sc + n * (cs * N) + Bl + N ^ 2 ≤ C0 * (w + S + N ^ 2 + Bl) := by
    linarith
  have hLa0 : 0 ≤ La := by linarith
  have h4 := mul_le_mul_of_nonneg_right hin hLa0
  have h5 := mul_le_mul_of_nonneg_left hLa (sq_nonneg N)
  nlinarith

lemma arith_fact_off {w S Sc N Bl cs C0 La n k : ℝ} (hw : 0 ≤ w) (_hSc0 : 0 ≤ Sc) (hBl : 0 ≤ Bl)
    (hn : 0 ≤ n) (hk : k = n + 1) (hkN : k ≤ N) (hcs : 0 ≤ cs) (hC2 : 2 ≤ C0) (hCcs : cs + 1 ≤ C0)
    (hSc : 2 * Sc ≤ C0 * S) (hLa : 1 ≤ La) :
    (w + 2 * Sc + n * (cs * N) + Bl) * La ≤ C0 * (w + S + N ^ 2 + Bl) * La := by
  have hnN := arith_nN hn (by linarith : n ≤ k) hkN hcs
  have hN2 : 0 ≤ N ^ 2 := sq_nonneg N
  have h1 := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ C0) hw
  have h2 := mul_le_mul_of_nonneg_right (by linarith : cs ≤ C0) hN2
  have h3 := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ C0) hBl
  have hin : w + 2 * Sc + n * (cs * N) + Bl ≤ C0 * (w + S + N ^ 2 + Bl) := by
    linarith
  exact mul_le_mul_of_nonneg_right hin (by linarith)

lemma arith_per {d w S Sc N Bl C0 n k X : ℝ} (hw : 0 ≤ w) (hSc0 : 0 ≤ Sc) (hBl : 0 ≤ Bl)
    (hn : 0 ≤ n) (hnk : n ≤ k) (hkN : k ≤ N) (hC2 : 2 ≤ C0) (hSc : 2 * Sc ≤ C0 * S) (hX : 0 ≤ X)
    (h1 : -w ≤ d) (h2 : d ≤ n * Sc + Bl) :
    |d| ≤ C0 * (w + k * (N + S) + Bl + X) := by
  have hk0 : 0 ≤ k := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hCS : 0 ≤ C0 * S := by linarith
  have hC0 : 0 ≤ C0 := by linarith
  have e1 := mul_le_mul_of_nonneg_right hnk hSc0
  have e2 := mul_le_mul_of_nonneg_left hSc hk0
  have e3 := mul_nonneg (mul_nonneg hC0 hk0) hN0
  have e4 := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ C0) hw
  have e5 := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ C0) hBl
  have e6 := mul_nonneg hC0 hX
  have e7 := mul_nonneg hk0 hCS
  rw [abs_le]
  constructor <;> nlinarith

lemma off_nonneg {n w : ℕ} {S Bl sh : ℝ} {ν ap : Multiset ℕ} (h : IsRowsOff n w S Bl sh ν ap) :
    0 ≤ S ∧ 0 ≤ Bl := by
  obtain ⟨c, c', r, blk, sm, hI, -, hblk, -, -⟩ := h
  exact ⟨le_trans (hI.1 0).1 (hI.1 0).2, le_trans (Nat.cast_nonneg _) hblk⟩

lemma top_nonneg {n aT w : ℕ} {S Bl sh : ℝ} {ν ap : Multiset ℕ}
    (h : IsRowsTop n aT w S Bl sh ν ap) : 0 ≤ S ∧ 0 ≤ Bl := by
  obtain ⟨c, c', r, r0, blk, sm, hI, -, -, hblk, -, -⟩ := h
  exact ⟨le_trans (hI.1 0).1 (hI.1 0).2, le_trans (Nat.cast_nonneg _) hblk⟩

end W8

theorem young_diagram_step : RowsStepE := by
  intro J Pl _ _ TT _ n aT w ν ap fa a rd La k N S Sc t η m b' cs C0 hLa hLa1 hk hkN hb' hcs hC2
    hCcs hSc hwA hBlA haTA hfa hoff htop
  have hk0 : 0 ≤ k := by
    rw [hk]
    positivity
  refine ⟨fun j ρ => phRows (ν j ρ) - fa j ρ - (if ρ ∈ TT then ph (aT ρ : ℝ) else 0),
    fun j ρ => ((ν j ρ).sum : ℝ) - (if ρ ∈ TT then (aT ρ : ℝ) else 0) - k * (w j ρ : ℝ),
    fun j ρ => by dsimp only; linarith, fun j ρ => by dsimp only; ring, fun j ρ => ?_, fun j ρ => ?_⟩
  · dsimp only
    by_cases hρ : ρ ∈ TT
    · rw [if_pos hρ]
      have hT := htop j ρ hρ
      have h0 := top_nonneg hT
      have hF := (young_diagram_factorial n (w j ρ) Sc (m * (t + 1) * η) (cs * N) (a * rd) La (fa j ρ)
        (ν j ρ) (ap j ρ) hLa hLa1 (hwA j ρ) hBlA (hfa j ρ)).2 (aT ρ) (haTA j ρ hρ) hT
      have hA := arith_fact_top (w := (w j ρ : ℝ)) (n := (n : ℝ)) (Nat.cast_nonneg _) h0.1 h0.2
        (Nat.cast_nonneg _) hk hkN hcs hC2 hCcs hSc hLa1
      linarith
    · rw [if_neg hρ]
      have hO := hoff j ρ hρ
      have h0 := off_nonneg hO
      have hF := (young_diagram_factorial (n + 1) (w j ρ) Sc (m * (t + 1) * η) (cs * N) (a * rd) La
        (fa j ρ) (ν j ρ) (ap j ρ) hLa hLa1 (hwA j ρ) hBlA (hfa j ρ)).1 hO
      have hA := arith_fact_off (w := (w j ρ : ℝ)) (n := ((n + 1 : ℕ) : ℝ)) (k := k)
        (Nat.cast_nonneg _) h0.1 h0.2 (Nat.cast_nonneg _) (by push_cast; linarith) hkN hcs hC2
        hCcs hSc hLa1
      linarith
  · dsimp only
    by_cases hρ : ρ ∈ TT
    · rw [if_pos hρ, if_pos hρ]
      have hT := htop j ρ hρ
      have h0 := top_nonneg hT
      have hP := (young_diagram_period n (w j ρ) Sc (m * (t + 1) * η) (cs * N) (ν j ρ) (ap j ρ)).2
        (aT ρ) hT
      have hX : 0 ≤ k * b' := mul_nonneg hk0 hb'
      have e1 : k * (w j ρ : ℝ) = ((n : ℝ) + 2) * (w j ρ : ℝ) := by rw [hk]
      obtain ⟨hP1, hP2⟩ := hP
      exact arith_per (n := (n : ℝ)) (k := k) (Nat.cast_nonneg _) h0.1 h0.2 (Nat.cast_nonneg _)
        (by rw [hk]; linarith) hkN hC2 hSc hX (by linarith) (by linarith)
    · rw [if_neg hρ, if_neg hρ]
      have hO := hoff j ρ hρ
      have h0 := off_nonneg hO
      have hP := (young_diagram_period (n + 1) (w j ρ) Sc (m * (t + 1) * η) (cs * N) (ν j ρ)
        (ap j ρ)).1 hO
      have e1 : k * (w j ρ : ℝ) = (((n + 1 : ℕ) : ℝ) + 1) * (w j ρ : ℝ) := by
        rw [hk]
        push_cast
        ring
      have e2 : k * Sc = (((n + 1 : ℕ) : ℝ) + 1) * Sc := by
        rw [hk]
        push_cast
        ring
      have hw0 : (0 : ℝ) ≤ w j ρ := Nat.cast_nonneg _
      obtain ⟨hP1, hP2⟩ := hP
      exact arith_per (n := k) (k := k) (Nat.cast_nonneg _) h0.1 h0.2 hk0 le_rfl hkN hC2 hSc le_rfl
        (by linarith) (by linarith)

end Formalism.DivisionValues
