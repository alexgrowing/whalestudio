import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.TailInt

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace J2

lemma lsq_zero {p m : ℕ} (x : Xp p m) : Lsq x 0 = 1 := by simp [Lsq]

lemma lsq_one {p m : ℕ} (x : Xp (p + 1) m) : Lsq x 1 = 1 + ‖x.1 0‖ ^ 2 := by
  simp [Lsq]

lemma rhoSq_zero {p m : ℕ} (x : Xp (p + 1) m) : rhoSq x 0 = rhoSq x 1 + ‖x.2.1 0‖ ^ 2 := by
  simp only [rhoSq, Fin.sum_univ_succ]
  simp
  ring_nf

lemma bco_zero {p m : ℕ} (x : Xp (p + 1) m) : bco x 0 = bco x 1 - x.2.1 0 * star (x.1 0) := by
  simp only [bco, Fin.sum_univ_succ]
  simp
  ring_nf

lemma one_le_lsq {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : 1 ≤ Lsq x l := by
  unfold Lsq
  have : 0 ≤ ∑ j : Fin p, (if j.val < l.val then ‖x.1 j‖ ^ 2 else 0) :=
    Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
  linarith

lemma rhoSq_nonneg {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : 0 ≤ rhoSq x l := by
  unfold rhoSq
  have h1 := one_le_lsq x (Fin.last p)
  have : 0 ≤ ∑ j : Fin p, (if l.val ≤ j.val then ‖x.2.1 j‖ ^ 2 else 0) :=
    Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
  have : 0 ≤ ∑ i, ‖x.2.2.1 i‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  linarith

lemma de_sq {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) :
    de x l ^ 2 = Lsq x l * rhoSq x l + ‖bco x l‖ ^ 2 := by
  unfold de
  rw [Real.sq_sqrt]
  have := one_le_lsq x l; have := rhoSq_nonneg x l
  positivity

lemma de_nonneg {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : 0 ≤ de x l := Real.sqrt_nonneg _

lemma one_le_rhoSq {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : 1 ≤ rhoSq x l := by
  unfold rhoSq
  have h1 := one_le_lsq x (Fin.last p)
  have : 0 ≤ ∑ j : Fin p, (if l.val ≤ j.val then ‖x.2.1 j‖ ^ 2 else 0) :=
    Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
  have : 0 ≤ ∑ i, ‖x.2.2.1 i‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  linarith

lemma de_pos {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : 0 < de x l := by
  unfold de
  apply Real.sqrt_pos.2
  have h1 := one_le_lsq x l; have h2 := one_le_rhoSq x l
  have : 0 ≤ ‖bco x l‖ ^ 2 := by positivity
  nlinarith

lemma rhoSq_cons {p m : ℕ} (a : Fin (p + 1) → ℂ) (w : ℂ) (b : Fin p → ℂ) (r : (Fin m → ℂ) × ℝ)
    (i : Fin (p + 1)) :
    rhoSq ((a, Fin.cons w b, r) : Xp (p + 1) m) i.succ = rhoSq ((a, Fin.cons 0 b, r) : Xp (p + 1) m) i.succ := by
  simp [rhoSq, Lsq, Fin.sum_univ_succ]

lemma bco_cons {p m : ℕ} (a : Fin (p + 1) → ℂ) (w : ℂ) (b : Fin p → ℂ) (r : (Fin m → ℂ) × ℝ)
    (i : Fin (p + 1)) :
    bco ((a, Fin.cons w b, r) : Xp (p + 1) m) i.succ = bco ((a, Fin.cons 0 b, r) : Xp (p + 1) m) i.succ := by
  simp [bco, Fin.sum_univ_succ]

lemma de_cons {p m : ℕ} (a : Fin (p + 1) → ℂ) (w : ℂ) (b : Fin p → ℂ) (r : (Fin m → ℂ) × ℝ)
    (i : Fin (p + 1)) :
    de ((a, Fin.cons w b, r) : Xp (p + 1) m) i.succ = de ((a, Fin.cons 0 b, r) : Xp (p + 1) m) i.succ := by
  simp only [de, rhoSq_cons, bco_cons]
  rfl

def sclPt {p m : ℕ} (a0 : ℂ) (r : ℝ) (x : Xp p m) :
    (Fin (p + 1) → ℂ) × (Fin p → ℂ) × (Fin m → ℂ) × ℝ :=
  (Fin.cons a0 (r • x.1), r • x.2.1, r • x.2.2.1, r ^ 2 * x.2.2.2)

lemma lsq_scl_one {p m : ℕ} (a0 : ℂ) (r : ℝ) (x : Xp p m) :
    Lsq (tailPt (sclPt a0 r x)) 1 = 1 + ‖a0‖ ^ 2 := by
  simp [Lsq, tailPt, sclPt]

lemma lsq_scl {p m : ℕ} (a0 : ℂ) (r : ℝ) (hr : 1 + ‖a0‖ ^ 2 = r ^ 2) (x : Xp p m) (i : Fin (p + 1)) :
    Lsq (tailPt (sclPt a0 r x)) i.succ = r ^ 2 * Lsq x i := by
  simp only [Lsq, tailPt, sclPt, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero,
    Fin.val_succ, Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  simp only [Nat.zero_lt_succ, if_true, add_lt_add_iff_right, mul_add, Finset.mul_sum, mul_ite, mul_zero]
  linarith

lemma rhoSq_scl {p m : ℕ} (a0 : ℂ) (r : ℝ) (hr : 1 + ‖a0‖ ^ 2 = r ^ 2) (x : Xp p m) (i : Fin (p + 1)) :
    rhoSq (tailPt (sclPt a0 r x)) i.succ = r ^ 2 * rhoSq x i := by
  have hl := lsq_scl a0 r hr x (Fin.last p)
  rw [Fin.succ_last] at hl
  unfold rhoSq
  rw [hl]
  simp only [tailPt, sclPt, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero,
    Fin.val_succ, Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  simp only [add_le_add_iff_right, mul_add, Finset.mul_sum, mul_ite, mul_zero]
  simp

lemma bco_scl {p m : ℕ} (a0 : ℂ) (r : ℝ) (x : Xp p m) (i : Fin (p + 1)) :
    bco (tailPt (sclPt a0 r x)) i.succ = ((r ^ 2 : ℝ) : ℂ) * bco x i := by
  simp only [bco, tailPt, sclPt, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero,
    Fin.val_succ, Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  simp only [add_le_add_iff_right, Complex.real_smul, star_mul',
    Complex.star_def, Complex.conj_ofReal]
  push_cast
  simp
  have s1 : ∑ j, (r : ℂ) ^ 2 * ((‖x.2.2.1 j‖ : ℂ)) ^ 2 = (r : ℂ) ^ 2 * ∑ j, ((‖x.2.2.1 j‖ : ℂ)) ^ 2 := by
    rw [Finset.mul_sum]
  have s2 : (∑ j : Fin p, if (i : ℕ) ≤ (j : ℕ) then (r : ℂ) * x.2.1 j * ((r : ℂ) * (starRingEnd ℂ) (x.1 j)) else 0)
      = (r : ℂ) ^ 2 * ∑ j : Fin p, if (i : ℕ) ≤ (j : ℕ) then x.2.1 j * (starRingEnd ℂ) (x.1 j) else 0 := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; split_ifs <;> ring
  rw [s1, s2]; ring

lemma de_scl {p m : ℕ} (a0 : ℂ) (r : ℝ) (hr : 1 + ‖a0‖ ^ 2 = r ^ 2) (x : Xp p m) (i : Fin (p + 1)) :
    de (tailPt (sclPt a0 r x)) i.succ = r ^ 2 * de x i := by
  have h := de_sq (tailPt (sclPt a0 r x)) i.succ
  rw [lsq_scl a0 r hr, rhoSq_scl a0 r hr, bco_scl, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg r)] at h
  have h2 := de_sq x i
  have : de (tailPt (sclPt a0 r x)) i.succ ^ 2 = (r ^ 2 * de x i) ^ 2 := by rw [h, mul_pow (r ^ 2) (de x i), h2]; ring
  have p1 := de_nonneg (tailPt (sclPt a0 r x)) i.succ
  have p2 := de_nonneg x i
  exact (pow_left_inj₀ p1 (by positivity) two_ne_zero).1 this

lemma cont_lsq {p m : ℕ} (l : Fin (p + 1)) : Continuous fun x : Xp p m => Lsq x l := by
  unfold Lsq
  exact continuous_const.add (continuous_finsetSum _ fun j _ => by split_ifs <;> fun_prop)

lemma cont_rhoSq {p m : ℕ} (l : Fin (p + 1)) : Continuous fun x : Xp p m => rhoSq x l := by
  unfold rhoSq
  refine ((cont_lsq _).add (continuous_finsetSum _ fun j _ => by fun_prop)).add
    (continuous_finsetSum _ fun j _ => by split_ifs <;> fun_prop)

lemma cont_bco {p m : ℕ} (l : Fin (p + 1)) : Continuous fun x : Xp p m => bco x l := by
  unfold bco
  refine Continuous.sub ?_ (continuous_finsetSum _ fun j _ => by split_ifs <;> fun_prop)
  fun_prop

lemma cont_de {p m : ℕ} (l : Fin (p + 1)) : Continuous fun x : Xp p m => de x l :=
  Real.continuous_sqrt.comp (((cont_lsq l).mul (cont_rhoSq l)).add ((cont_bco l).norm.pow 2))

lemma cont_cons {p : ℕ} : Continuous fun q : ℂ × (Fin p → ℂ) => (Fin.cons q.1 q.2 : Fin (p + 1) → ℂ) := by
  refine continuous_pi fun j => ?_
  refine Fin.cases ?_ (fun i => ?_) j
  · simpa using continuous_fst
  · simp only [Fin.cons_succ]
    exact (continuous_apply i).comp continuous_snd

lemma cont_tailPt {p m : ℕ} :
    Continuous (tailPt : (Fin (p + 1) → ℂ) × (Fin p → ℂ) × (Fin m → ℂ) × ℝ → Xp (p + 1) m) := by
  unfold tailPt
  exact continuous_fst.prodMk ((cont_cons.comp (continuous_const.prodMk
    (continuous_fst.comp continuous_snd))).prodMk (continuous_snd.comp continuous_snd))

end J2
end ReciprocityTheory.ChartRestriction.DS.Xi
