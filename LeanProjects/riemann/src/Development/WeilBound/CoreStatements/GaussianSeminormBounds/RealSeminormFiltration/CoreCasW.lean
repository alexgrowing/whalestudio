import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreDefs

noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

def rho2 {r s : ℕ} : Ix r s → ℚ
  | .inl k => (r : ℚ) - 1 - 2 * (k : ℕ)
  | .inr l => (s : ℚ) - 1 - 2 * (l : ℕ)

theorem cw_cnt_lt {n : ℕ} (i : Fin n) (c : ℚ) :
    ∑ j : Fin n, (if i < j then c else 0) = ((n : ℚ) - 1 - (i : ℕ)) * c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
  have h := i.2
  rw [Nat.sub_sub, Nat.cast_sub (by omega)]
  push_cast
  ring

theorem cw_cnt_gt {n : ℕ} (j : Fin n) (c : ℚ) :
    ∑ i : Fin n, (if i < j then c else 0) = ((j : ℕ) : ℚ) * c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, Finset.filter_gt_eq_Iio, Fin.card_Iio]

theorem cw_blk {n : ℕ} (f : Fin n → ℚ) :
    ∑ i, ∑ j, (if i < j then f i - f j else 0) = ∑ i : Fin n, ((n : ℚ) - 1 - 2 * (i : ℕ)) * f i := by
  have e : ∀ i j : Fin n, (if i < j then f i - f j else 0) = (if i < j then f i else 0) - (if i < j then f j else 0) := by
    intro i j
    split_ifs <;> ring
  simp_rw [e, Finset.sum_sub_distrib, cw_cnt_lt]
  rw [Finset.sum_comm (f := fun i j => if i < j then f j else 0)]
  simp_rw [cw_cnt_gt]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem cw_two {ι : Type} [Fintype ι] [DecidableEq ι] (G H : ι → ℚ) {a b : ι} (hab : a ≠ b)
    (h : ∀ x, x ≠ a → x ≠ b → G x = H x) : ∑ x, G x = ∑ x, H x + (G b - H b) + (G a - H a) := by
  have key : ∑ x, (G x - H x) = (G a - H a) + (G b - H b) :=
    Fintype.sum_eq_add a b hab (fun x hx => by rw [h x hx.1 hx.2, sub_self])
  rw [Finset.sum_sub_distrib] at key
  linarith

theorem cw_root {r s : ℕ} {ν La : Ix r s → ℚ} {a b : Ix r s} (hab : a ≠ b) (h : RootTo ν a b La) :
    ν a = La a - 1 ∧ ν b = La b + 1 ∧ ∀ x, x ≠ a → x ≠ b → ν x = La x := by
  refine ⟨?_, ?_, ?_⟩
  · have := h a
    rw [if_pos rfl, if_neg hab] at this
    linarith
  · have := h b
    rw [if_neg (Ne.symm hab), if_pos rfl] at this
    linarith
  · intro x hxa hxb
    have := h x
    rw [if_neg hxa, if_neg hxb] at this
    linarith

theorem cw_init {r p : ℕ} (hp : p ≤ r) (c : ℚ) :
    ∑ k : Fin r, (if (k : ℕ) < p then c else 0) = p * c := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if k < p then c else 0) r, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have e : (Finset.range r).filter (fun k => k < p) = Finset.range p := by
    ext k
    simp
    omega
  rw [e, Finset.card_range]

theorem cw_fin {r q : ℕ} (hq : q ≤ r) (c : ℚ) :
    ∑ k : Fin r, (if r ≤ (k : ℕ) + q then c else 0) = q * c := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if r ≤ k + q then c else 0) r, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have e : (Finset.range r).filter (fun k => r ≤ k + q) = Finset.Ico (r - q) r := by
    ext k
    simp
    omega
  rw [e, Nat.card_Ico, show r - (r - q) = q by omega]

theorem casW_eq {r s : ℕ} (μ : Ix r s → ℚ) : casW μ = ∑ x, μ x ^ 2 + ∑ x, rho2 x * μ x := by
  unfold casW
  congr 1
  simp only [Fintype.sum_sum_type, posC, rho2]
  simp only [if_false, ite_false, Finset.sum_const_zero, add_zero, zero_add]
  rw [cw_blk, cw_blk]

theorem casW_root {r s : ℕ} {ν La : Ix r s → ℚ} {a b : Ix r s} (hab : a ≠ b) (h : RootTo ν a b La) :
    casW ν = casW La + 2 * (La b - La a) + 2 + (rho2 b - rho2 a) := by
  obtain ⟨ha, hb, hx⟩ := cw_root hab h
  rw [casW_eq, casW_eq, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have key := cw_two (fun x => ν x ^ 2 + rho2 x * ν x) (fun x => La x ^ 2 + rho2 x * La x) hab
    (fun x h1 h2 => by simp only [hx x h1 h2])
  simp only [ha, hb] at key
  linear_combination key

private theorem shiftNu_sub_lemma {r s : ℕ} (c : ℚ) (μ μ' : Ix r s → ℚ) (x : Ix r s) :
    shiftNu c μ x = shiftNu c μ' x + (μ x - μ' x) := by
  cases x <;> simp only [shiftNu] <;> ring

theorem degW_root {r s : ℕ} (c : ℚ) {ν La : Ix r s → ℚ} {a b : Ix r s} (hab : a ≠ b) (h : RootTo ν a b La) :
    degW c ν = degW c La + (|shiftNu c La b + 1| - |shiftNu c La b|) + (|shiftNu c La a - 1| - |shiftNu c La a|) := by
  obtain ⟨ha, hb, hx⟩ := cw_root hab h
  have key := cw_two (fun x => |shiftNu c ν x|) (fun x => |shiftNu c La x|) hab
    (fun x h1 h2 => by
      show |shiftNu c ν x| = |shiftNu c La x|
      rw [shiftNu_sub_lemma c ν La x, hx x h1 h2, sub_self, add_zero])
  have e1 : shiftNu c ν b = shiftNu c La b + 1 := by
    rw [shiftNu_sub_lemma c ν La b, hb]
    ring
  have e2 : shiftNu c ν a = shiftNu c La a - 1 := by
    rw [shiftNu_sub_lemma c ν La a, ha]
    ring
  simp only [e1, e2] at key
  unfold degW
  exact key

theorem degW_laPos {p q r s n m : ℕ} (hp : p ≤ r) (hq : q ≤ s) :
    degW (cPair p q) (laPos p q r s n m) = p * n + q * m := by
  unfold degW
  rw [Fintype.sum_sum_type]
  simp only [shiftNu, laPos, add_sub_cancel_right, sub_add_cancel]
  have e : ∀ (P : Prop) [Decidable P] (t : ℕ), |(if P then (t : ℚ) else 0)| = if P then (t : ℚ) else 0 := by
    intro P _ t
    split_ifs <;> simp
  simp only [e]
  rw [cw_init hp, cw_init hq]

theorem degW_laNeg {p q r s n m : ℕ} (hq : q ≤ r) (hp : p ≤ s) :
    degW (cPair p q) (laNeg p q r s n m) = q * n + p * m := by
  unfold degW
  rw [Fintype.sum_sum_type]
  simp only [shiftNu, laNeg, add_sub_cancel_right, sub_add_cancel]
  have e : ∀ (P : Prop) [Decidable P] (t : ℕ), |(if P then -(t : ℚ) else 0)| = if P then (t : ℚ) else 0 := by
    intro P _ t
    split_ifs <;> simp
  simp only [e]
  rw [cw_fin hq, cw_fin hp]

theorem degW_const {p q : ℕ} (c c0 : ℚ) :
    degW c (fun _ : Ix p q => c0) = p * |c0 - c| + q * |c0 + c| := by
  unfold degW
  simp [Fintype.sum_sum_type, shiftNu]

end PositivityTheory.KReal

end
