import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.OrbitIntegralAbsConvergent

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section NHeisAux

variable (k r' : ℕ)

def nhLst : Fin (2 * (1 + r') + k + 1) := ⟨2 * (1 + r') + k, by omega⟩

def nhFst : Fin (2 * (1 + r') + k + 1) := ⟨0, by omega⟩

def nhSh (i : Fin (2 * r' + k + 1)) : Fin (2 * (1 + r') + k + 1) := ⟨i.val + 1, by omega⟩

theorem e0_eq_single_nhFst : e0 k r' = Pi.single (nhFst k r') 1 := rfl

theorem herm_basisVec_e0 (j : Fin (2 * (1 + r') + k + 1)) :
    herm (Hpk k (1 + r')) (bvec j) (e0 k r') = if j = nhLst k r' then 1 else 0 := by
  rw [herm, e0_eq_single_nhFst, bvec, mulVec_single_one, ← Pi.single_star, star_one, single_dotProduct,
    one_mul, col_apply]
  have hj : (j = nhLst k r') ↔ j.val = 2 * (1 + r') + k := by simp [nhLst, Fin.ext_iff]
  simp only [Hpk, nhFst, hj, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem nh_herm_lst_lift (y : Fin (2 * r' + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) (bvec (nhLst k r')) (liftVec k 1 r' y) = 0 := by
  rw [herm, bvec, mulVec_single_one, dotProduct]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i.val = 0
  · simp [liftVec, hi]
  · simp only [Hpk, nhLst, col_apply, Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | simp

theorem nh_heisG_apply (v : Fin (2 * (1 + r') + k + 1) → ℂ) (b : ℂ) (p t : Fin (2 * (1 + r') + k + 1)) :
    heisG k r' v b p t = (if p = t then 1 else 0) - e0 k r' p * herm (Hpk k (1 + r')) (bvec t) v +
      (v p + b * e0 k r' p) * (if t = nhLst k r' then 1 else 0) := by
  simp only [heisG, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, vecMulVec_apply, herm_basisVec_e0,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem nh_iota_lst (n' : Mat k r') (t : Fin (2 * (1 + r') + k + 1)) :
    ιLev k 1 r' n' t (nhLst k r') = if t = nhLst k r' then 1 else 0 := by
  unfold ιLev
  have h : ¬ (1 ≤ (nhLst k r').val ∧ (nhLst k r').val < 2 * r' + k + 1 + 1) := by simp [nhLst]; omega
  split_ifs with h1 h2 h3
  all_goals first | rfl | (exfalso; subst_vars; exact h ‹_›)

theorem nh_iota_lst_row (n' : Mat k r') (q : Fin (2 * (1 + r') + k + 1)) :
    ιLev k 1 r' n' (nhLst k r') q = if q = nhLst k r' then 1 else 0 := by
  unfold ιLev
  have h : ¬ (1 ≤ (nhLst k r').val ∧ (nhLst k r').val < 2 * r' + k + 1 + 1) := by simp [nhLst]; omega
  rw [dif_neg h]
  by_cases hq : q = nhLst k r'
  · simp [hq]
  · rw [if_neg (Ne.symm hq), if_neg hq]

theorem nh_iota_sh (n' : Mat k r') (i j : Fin (2 * r' + k + 1)) :
    ιLev k 1 r' n' (nhSh k r' i) (nhSh k r' j) = n' i j := by
  unfold ιLev
  have hi : 1 ≤ (nhSh k r' i).val ∧ (nhSh k r' i).val < 2 * r' + k + 1 + 1 := by simp [nhSh]; omega
  have hj : 1 ≤ (nhSh k r' j).val ∧ (nhSh k r' j).val < 2 * r' + k + 1 + 1 := by simp [nhSh]; omega
  rw [dif_pos hi, dif_pos hj]
  congr 1

theorem nh_lift_sh (y : Fin (2 * r' + k + 1) → ℂ) (i : Fin (2 * r' + k + 1)) :
    liftVec k 1 r' y (nhSh k r' i) = y i := by
  unfold liftVec
  have hi : 1 ≤ (nhSh k r' i).val ∧ (nhSh k r' i).val < 2 * r' + k + 1 + 1 := by simp [nhSh]; omega
  rw [dif_pos hi]
  congr 1

theorem nh_lift_fst (y : Fin (2 * r' + k + 1) → ℂ) : liftVec k 1 r' y (nhFst k r') = 0 := by
  simp [liftVec, nhFst]

theorem nh_row (x : HPar k r') (n' : Mat k r') (p q : Fin (2 * (1 + r') + k + 1)) (hp : p ≠ nhFst k r') :
    (heis0 k r' x * ιLev k 1 r' n') p q =
      ιLev k 1 r' n' p q + liftVec k 1 r' x.1 p * ιLev k 1 r' n' (nhLst k r') q := by
  have he : e0 k r' p = 0 := by rw [e0_eq_single_nhFst, Pi.single_apply, if_neg hp]
  rw [heis0, mul_apply]
  simp only [nh_heisG_apply, he, zero_mul, sub_zero, mul_zero, add_zero, add_mul, ite_mul, one_mul,
    zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_assoc]
  rw [← Finset.mul_sum]
  simp [Finset.sum_ite_eq']

theorem nh_corner (x : HPar k r') (n' : Mat k r') :
    (heis0 k r' x * ιLev k 1 r' n') (nhFst k r') (nhLst k r') = hb k r' x.1 x.2 := by
  rw [heis0, mul_apply]
  simp only [nh_iota_lst, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [nh_heisG_apply, nh_herm_lst_lift, nh_lift_fst, e0_eq_single_nhFst]
  have : nhFst k r' ≠ nhLst k r' := by simp [nhFst, nhLst, Fin.ext_iff]; omega
  simp [this]

theorem nh_sum_le {β α : Type*} [Fintype β] [Fintype α] [DecidableEq β] (g : β → ℝ) (hg : ∀ z, 0 ≤ g z)
    (F : α → β) (hF : Function.Injective F) : ∑ a, g (F a) ≤ ∑ z, g z := by
  rw [← Finset.sum_image (fun a _ b _ h => hF h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun z _ _ => hg z)

def nhF : (Fin (2 * r' + k + 1) × Fin (2 * r' + k + 1)) ⊕ Option (Fin (2 * r' + k + 1)) →
    Fin (2 * (1 + r') + k + 1) × Fin (2 * (1 + r') + k + 1)
  | Sum.inl ij => (nhSh k r' ij.1, nhSh k r' ij.2)
  | Sum.inr (some i) => (nhSh k r' i, nhLst k r')
  | Sum.inr none => (nhFst k r', nhLst k r')

theorem nhF_inj : Function.Injective (nhF k r') := by
  intro a b h
  have h1 : (nhF k r' a).1.val = (nhF k r' b).1.val := by rw [h]
  have h2 : (nhF k r' a).2.val = (nhF k r' b).2.val := by rw [h]
  rcases a with ⟨i, j⟩ | _ | i <;> rcases b with ⟨i', j'⟩ | _ | i' <;>
    dsimp only [nhF, nhSh, nhLst, nhFst, Fin.val_mk] at h1 h2
  all_goals first | rfl | (exfalso; omega) | skip
  · have hi : i = i' := Fin.ext (by omega)
    have hj : j = j' := Fin.ext (by omega)
    rw [hi, hj]
  · have hi : i = i' := Fin.ext (by omega)
    rw [hi]

theorem nh_sh_ne_fst (i : Fin (2 * r' + k + 1)) : nhSh k r' i ≠ nhFst k r' := by
  intro h; have h' := congrArg Fin.val h; dsimp only [nhSh, nhFst, Fin.val_mk] at h'; omega

theorem nh_sh_ne_lst (i : Fin (2 * r' + k + 1)) : nhSh k r' i ≠ nhLst k r' := by
  intro h; have h' := congrArg Fin.val h; dsimp only [nhSh, nhLst, Fin.val_mk] at h'; omega

theorem nh_entry_sh (x : HPar k r') (n' : Mat k r') (i j : Fin (2 * r' + k + 1)) :
    (heis0 k r' x * ιLev k 1 r' n') (nhSh k r' i) (nhSh k r' j) = n' i j := by
  rw [nh_row k r' x n' _ _ (nh_sh_ne_fst k r' i), nh_iota_sh, nh_iota_lst_row, if_neg (nh_sh_ne_lst k r' j),
    mul_zero, add_zero]

theorem nh_entry_col (x : HPar k r') (n' : Mat k r') (i : Fin (2 * r' + k + 1)) :
    (heis0 k r' x * ιLev k 1 r' n') (nhSh k r' i) (nhLst k r') = x.1 i := by
  rw [nh_row k r' x n' _ _ (nh_sh_ne_fst k r' i), nh_iota_lst, if_neg (nh_sh_ne_lst k r' i), nh_iota_lst_row,
    if_pos rfl, mul_one, zero_add, nh_lift_sh]

theorem nh_gN_sq {a b : ℕ} (M : Mat a b) : gN M ^ 2 = ∑ p, ∑ q, Complex.normSq (M p q) := by
  rw [gN]
  exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)

theorem nh_hb_normSq (y : Fin (2 * r' + k + 1) → ℂ) (s : ℝ) : s ^ 2 ≤ Complex.normSq (hb k r' y s) := by
  have him : (hb k r' y s).im = s := by simp [hb]
  rw [Complex.normSq_apply, him]
  nlinarith [mul_self_nonneg (hb k r' y s).re]

theorem nh_cont_lift : Continuous (fun y : Fin (2 * r' + k + 1) → ℂ => liftVec k 1 r' y) := by
  refine continuous_pi fun p => ?_
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · simp only [liftVec, dif_pos hp]; exact continuous_apply _
  · simp only [liftVec, dif_neg hp]; exact continuous_const

theorem nh_cont_herm {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (w : Fin m → ℂ) :
    Continuous (fun v : Fin m → ℂ => herm H w v) := by
  unfold herm dotProduct; fun_prop

theorem nh_cont_herm_diag {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) :
    Continuous (fun v : Fin m → ℂ => herm H v v) := by
  unfold herm dotProduct mulVec dotProduct; fun_prop

theorem nh_cont_hb : Continuous (fun x : HPar k r' => hb k r' x.1 x.2) := by
  have h := (nh_cont_herm_diag (Hpk k r')).comp (continuous_fst (X := Fin (2 * r' + k + 1) → ℂ) (Y := ℝ))
  unfold hb
  have h2 : Continuous fun x : HPar k r' => (-(herm (Hpk k r') x.1 x.1).re / 2 : ℝ) :=
    ((Complex.continuous_re.comp h).neg).div_const _
  exact (Complex.continuous_ofReal.comp h2).add ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)

end NHeisAux

theorem gN_heis_lev (k r' : ℕ) (x : HPar k r') (n' : Mat k r') :
    gN n' ^ 2 + ∑ i, Complex.normSq (x.1 i) + x.2 ^ 2 ≤ gN (heis0 k r' x * ιLev k 1 r' n') ^ 2 := by
  have e1 := nh_entry_sh k r' x n'
  have e2 := nh_entry_col k r' x n'
  have e3 := nh_corner k r' x n'
  rw [nh_gN_sq, nh_gN_sq]
  generalize heis0 k r' x * ιLev k 1 r' n' = G at e1 e2 e3 ⊢
  have key := nh_sum_le (fun z : Fin (2 * (1 + r') + k + 1) × Fin (2 * (1 + r') + k + 1) =>
    Complex.normSq (G z.1 z.2)) (fun z => Complex.normSq_nonneg _) (nhF k r') (nhF_inj k r')
  have hsum : ∑ z : Fin (2 * (1 + r') + k + 1) × Fin (2 * (1 + r') + k + 1), Complex.normSq (G z.1 z.2) =
      ∑ p, ∑ q, Complex.normSq (G p q) := Fintype.sum_prod_type' (fun p q => Complex.normSq (G p q))
  have hsum' : ∑ z : Fin (2 * r' + k + 1) × Fin (2 * r' + k + 1), Complex.normSq (n' z.1 z.2) =
      ∑ p, ∑ q, Complex.normSq (n' p q) := Fintype.sum_prod_type' (fun p q => Complex.normSq (n' p q))
  rw [hsum] at key
  refine le_trans ?_ key
  simp only [Fintype.sum_sum_type, Fintype.sum_option, nhF, e1, e2, e3]
  rw [hsum']
  have := nh_hb_normSq k r' x.1 x.2
  linarith

theorem continuous_heis0 (k r' : ℕ) : Continuous (fun x : HPar k r' => (heis0 k r' x : Mt k (1 + r'))) := by
  refine continuous_pi fun p => continuous_pi fun t => ?_
  simp only [heis0, nh_heisG_apply]
  have hl := (nh_cont_lift k r').comp (continuous_fst (X := Fin (2 * r' + k + 1) → ℂ) (Y := ℝ))
  have h1 := (continuous_apply p).comp hl
  have h2 := (nh_cont_herm (Hpk k (1 + r')) (bvec t)).comp hl
  exact (continuous_const.sub (continuous_const.mul h2)).add
    ((h1.add ((nh_cont_hb k r').mul continuous_const)).mul continuous_const)

end ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A
