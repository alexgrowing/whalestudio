import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFPrimeB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.LowFock
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CARUnit

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

abbrev tco (s : Finset (Fin (n * n))) (y : TensorProduct ℂ M (Fock n)) : M :=
  tcoef ((fockBasis n).coord s) y

def tform (y y' : TensorProduct ℂ M (Fock n)) : ℂ :=
  ∑ s, inner ℂ (tco s y) (tco s y')

theorem tform_conj (y y' : TensorProduct ℂ M (Fock n)) : star (tform y y') = tform y' y := by
  unfold tform
  rw [star_sum]
  exact sum_congr rfl fun s _ => inner_conj_symm _ _

theorem tform_sum_left {ι : Type*} (t : Finset ι) (f : ι → TensorProduct ℂ M (Fock n))
    (y' : TensorProduct ℂ M (Fock n)) : tform (∑ i ∈ t, f i) y' = ∑ i ∈ t, tform (f i) y' := by
  unfold tform
  simp only [map_sum, sum_inner]
  exact sum_comm

theorem tform_sum_right {ι : Type*} (t : Finset ι) (f : ι → TensorProduct ℂ M (Fock n))
    (y : TensorProduct ℂ M (Fock n)) : tform y (∑ i ∈ t, f i) = ∑ i ∈ t, tform y (f i) := by
  unfold tform
  simp only [map_sum, inner_sum]
  exact sum_comm

theorem tform_neg_left (y y' : TensorProduct ℂ M (Fock n)) : tform (-y) y' = -tform y y' := by
  unfold tform
  simp [inner_neg_left]

theorem tform_neg_right (y y' : TensorProduct ℂ M (Fock n)) : tform y (-y') = -tform y y' := by
  unfold tform
  simp [inner_neg_right]

theorem tform_add_left (y z y' : TensorProduct ℂ M (Fock n)) :
    tform (y + z) y' = tform y y' + tform z y' := by
  unfold tform
  simp [sum_add_distrib]

theorem tform_add_right (y y' z : TensorProduct ℂ M (Fock n)) :
    tform y (y' + z) = tform y y' + tform y z := by
  unfold tform
  simp [sum_add_distrib]

theorem tform_smul_right (c : ℂ) (y y' : TensorProduct ℂ M (Fock n)) :
    tform y (c • y') = c * tform y y' := by
  unfold tform
  simp [mul_sum]

theorem tform_self_re (y : TensorProduct ℂ M (Fock n)) : (tform y y).re = ∑ s, ‖tco s y‖ ^ 2 := by
  unfold tform
  rw [Complex.re_sum]
  refine sum_congr rfl fun s _ => ?_
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

theorem tform_self_re_nonneg (y : TensorProduct ℂ M (Fock n)) : 0 ≤ (tform y y).re := by
  rw [tform_self_re]
  exact sum_nonneg fun s _ => sq_nonneg _

theorem tform_self_re_pos {y : TensorProduct ℂ M (Fock n)} (hy : y ≠ 0) : 0 < (tform y y).re := by
  rcases (tform_self_re_nonneg y).lt_or_eq with h | h
  · exact h
  exfalso
  rw [tform_self_re] at h
  have h0 : ∀ s, tcoef ((fockBasis n).coord s) y = 0 := by
    intro s
    have hs := (sum_eq_zero_iff_of_nonneg (fun t _ => sq_nonneg ‖tco t y‖)).mp h.symm s (mem_univ s)
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hs)
  apply hy
  rw [tcoef_expand y]
  exact sum_eq_zero fun s _ => by rw [h0 s, TensorProduct.zero_tmul]

theorem tco_map_left (T : Module.End ℂ M) (s : Finset (Fin (n * n))) (y : TensorProduct ℂ M (Fock n)) :
    tco s (TensorProduct.map T LinearMap.id y) = T (tco s y) :=
  tcoef_map_left _ T y

theorem tco_lTensor (g : Module.End ℂ (Fock n)) (s : Finset (Fin (n * n))) (y : TensorProduct ℂ M (Fock n)) :
    tco s (TensorProduct.map LinearMap.id g y) =
      ∑ t, (fockBasis n).repr (g (fockBasis n t)) s • tco t y := by
  conv_lhs => rw [tcoef_expand y]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply, tcoef_tmul, Module.Basis.coord_apply]

theorem tform_eT {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hU : IsInfUnitary ε E) (a b : Fin n)
    (y y' : TensorProduct ℂ M (Fock n)) :
    tform (eT E a b y) y' = adjSign ε a b * tform y (eT E b a y') := by
  unfold tform eT
  simp only [tco_map_left, mul_sum]
  exact sum_congr rfl fun s _ => hU a b _ _

theorem tform_cpT (i a : Fin n) (y y' : TensorProduct ℂ M (Fock n)) :
    tform (cpT i a y) y' = tform y (cmT i a y') := by
  unfold tform cpT cmT
  simp only [tco_lTensor, sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  rw [sum_comm]
  refine sum_congr rfl fun t _ => sum_congr rfl fun s _ => ?_
  congr 1
  have h1 := lf_repr_cp_star (i, a) t s
  have h2 := lf_repr_cm_eq (i, a) s t
  rw [h2, starRingEnd_apply]
  exact h1

theorem tform_cmT (i a : Fin n) (y y' : TensorProduct ℂ M (Fock n)) :
    tform (cmT i a y) y' = tform y (cpT i a y') := by
  rw [← tform_conj y' (cmT i a y), ← tform_cpT, tform_conj]

theorem tform_dOp {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hU : IsInfUnitary ε E)
    (y y' : TensorProduct ℂ M (Fock n)) :
    tform (dOp ε (eT E) cpT y) y' = tform y (dOp' ε (eT E) cmT y') := by
  unfold dOp dOp'
  simp only [LinearMap.sum_apply, LinearMap.neg_apply, tform_sum_left, tform_neg_right, tform_sum_right,
    Module.End.mul_apply, ← sum_neg_distrib]
  refine sum_congr rfl fun i hi => sum_congr rfl fun a ha => ?_
  simp only [plusIdx, minusIdx, mem_filter, mem_univ, true_and] at hi ha
  rw [tform_eT hU, tform_cpT]
  have hc : cmT i a (eT E i a y') = eT E i a (cmT i a y') := by
    have := LinearMap.congr_fun ((eT_commutesCAR (n := n) E) i a i a).2 y'
    simp only [Module.End.mul_apply] at this
    exact this.symm
  rw [hc]
  simp [adjSign, hi, ha]

theorem tform_D {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hU : IsInfUnitary ε E)
    (y y' : TensorProduct ℂ M (Fock n)) :
    tform ((dOp ε (eT E) cpT + dOp' ε (eT E) cmT) y) y' =
      tform y ((dOp ε (eT E) cpT + dOp' ε (eT E) cmT) y') := by
  have h' : tform (dOp' ε (eT E) cmT y) y' = tform y (dOp ε (eT E) cpT y') := by
    rw [← tform_conj y' (dOp' ε (eT E) cmT y), ← tform_dOp hU, tform_conj]
  rw [LinearMap.add_apply, LinearMap.add_apply, tform_add_left, tform_add_right, tform_dOp hU, h', add_comm]

section Shift

theorem ssh_root_le (a b c : Fin n) : root a b c ≤ 1 := by
  unfold root
  simp only [Pi.sub_apply, Pi.single_apply]
  split_ifs <;> norm_num

theorem ssh_root_ge (a b c : Fin n) : -1 ≤ root a b c := by
  unfold root
  simp only [Pi.sub_apply, Pi.single_apply]
  split_ifs <;> norm_num

theorem ssh_rhoN_consec (ε : Fin n → Bool) {x y : Fin n} (hxy : x < y) (he : ε x = ε y)
    (hc : ∀ c, x < c → c < y → False) : rhoN ε x = rhoN ε y := by
  have h := lfD_cnt (fun c => ε c ≠ ε x) hxy
  have h1 : (univ.filter fun c => c = x ∧ ε c ≠ ε x).card = 0 := by
    rw [lfD_single]; simp
  have h2 : (univ.filter fun c => c = y ∧ ε c ≠ ε x).card = 0 := by
    rw [lfD_single]; simp [he]
  have h3 : (univ.filter fun c => x < c ∧ c < y ∧ ε c ≠ ε x).card = 0 := by
    rw [card_eq_zero, filter_eq_empty_iff]
    intro c _ hc'
    exact hc c hc'.1 hc'.2.1
  simp only [rhoN, ← he]
  rw [h1, h2, h3] at h
  have h' := congrArg (Nat.cast : ℕ → ℝ) h
  push_cast at h'
  linarith

theorem ssh_strictAnti {ε : Fin n → Bool} {lam : Fin n → ℝ} (hmono : StrictAnti lam) {h : ℝ}
    (hh : GapAtLeast ε lam h) (h2 : 2 < h) {N : Type*} [AddCommGroup N] [Module ℂ N]
    {E : Fin n → Fin n → Module.End ℂ N} (hE : IsGlRep E) (a b : Fin n) {W : Submodule ℂ N}
    (hW : IsKIrrHW ε E (lowK ε (lam - root a b)) W) : StrictAnti (lam - root a b) := by
  have hF : Formalism.REAL.KRel ε E := fun a b c d _ _ => hE a b c d
  cases n with
  | zero => exact fun x => x.elim0
  | succ m =>
    rw [Fin.strictAnti_iff_succ_lt]
    intro i
    have hxy : i.castSucc < i.succ := Fin.castSucc_lt_succ
    have hl := hmono hxy
    simp only [Pi.sub_apply]
    by_cases he : ε i.castSucc = ε i.succ
    · obtain ⟨N, hN⟩ := HW.kIrrHW_int ε hF hW _ _ hxy he
      have hbet : ∀ c, i.castSucc < c → c < i.succ → False := by
        intro c h1 h2
        rw [Fin.lt_def] at h1 h2
        simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
        omega
      have hC := HW.rhoC_consec ε hxy he (fun c h1 h2 => (hbet c h1 h2).elim)
      have hN' := ssh_rhoN_consec ε hxy he hbet
      simp only [lowK, Pi.add_apply, Pi.sub_apply] at hN
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg _
      linarith
    · have hg := hh _ _ he
      rw [abs_of_pos (sub_pos.mpr hl)] at hg
      have := ssh_root_le a b i.castSucc
      have := ssh_root_ge a b i.succ
      linarith

theorem ssh_casimir_eT {N : Type*} [AddCommGroup N] [Module ℂ N] (E : Fin n → Fin n → Module.End ℂ N) :
    casimir (eT (n := n) E) = TensorProduct.map (casimir E) LinearMap.id := by
  apply TensorProduct.ext'
  intro m f
  simp [casimir, eT, LinearMap.sum_apply, TensorProduct.sum_tmul]

theorem ssh_nsq_sub_root (lam : Fin n → ℝ) {a b : Fin n} (hab : a ≠ b) :
    nsq (lam - root a b) = nsq lam - 2 * (lam a - lam b) + 2 := by
  have e : nsq (lam - root a b) = nsq lam - 2 * dot (root a b) lam + dot (root a b) (root a b) := by
    unfold nsq dot
    rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun c _ => ?_
    simp only [Pi.sub_apply]
    ring
  rw [e, dot_root_left, dot_root_left]
  have ha : root a b a = 1 := by simp [root, hab]
  have hb : root a b b = -1 := by simp [root, Ne.symm hab]
  rw [ha, hb]
  ring

end Shift

end ReciprocityTheory.ChartRestriction.DS
