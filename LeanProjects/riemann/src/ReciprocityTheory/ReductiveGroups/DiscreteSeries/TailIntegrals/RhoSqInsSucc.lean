import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Imports

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace OSAux

abbrev Yp (p m : ℕ) := (Fin (p + 1) → ℂ) × (Fin p → ℂ) × (Fin m → ℂ) × ℝ

def ins {p m : ℕ} (y : Yp p m) (z : ℂ) : Xp (p + 1) m := (y.1, Fin.cons z y.2.1, y.2.2)

def bS {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : ℂ :=
  ∑ j : Fin p, if l.val ≤ j.val then x.2.1 j * star (x.1 j) else 0

lemma tailPt_eq {p m : ℕ} (y : Yp p m) : tailPt y = ins y 0 := rfl

lemma Lsq_ins {p m : ℕ} (y : Yp p m) (z : ℂ) (l : Fin (p + 2)) :
    Lsq (ins y z) l = Lsq (tailPt y) l := rfl

private theorem ins_snd_fst_eq_tailPt_snd_fst_of_ne_zero {p m : ℕ} (y : Yp p m) (z : ℂ) {j : Fin (p + 1)} (hj : j ≠ 0) :
    (ins y z).2.1 j = (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y).2.1 j := by
  induction j using Fin.cases with
  | zero => exact absurd rfl hj
  | succ k => simp [ins, ReciprocityTheory.ChartRestriction.DS.Xi.tailPt]

lemma sum_ins_succ {p m : ℕ} (y : Yp p m) (z : ℂ) (i : Fin (p + 1)) (g : ℂ → ℂ → ℂ) :
    (∑ j : Fin (p + 1), if i.succ.val ≤ j.val then g ((ins y z).2.1 j) ((ins y z).1 j) else 0) =
      ∑ j : Fin (p + 1), if i.succ.val ≤ j.val then g ((tailPt y).2.1 j) ((tailPt y).1 j) else 0 := by
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h : i.succ.val ≤ j.val
  · have hj : j ≠ 0 := by
      rintro rfl
      simp at h
    rw [if_pos h, if_pos h, ins_snd_fst_eq_tailPt_snd_fst_of_ne_zero y z hj]
    all_goals rfl
  · rw [if_neg h, if_neg h]

lemma sumR_ins_succ {p m : ℕ} (y : Yp p m) (z : ℂ) (i : Fin (p + 1)) :
    (∑ j : Fin (p + 1), if i.succ.val ≤ j.val then ‖(ins y z).2.1 j‖ ^ 2 else 0) =
      ∑ j : Fin (p + 1), if i.succ.val ≤ j.val then ‖(tailPt y).2.1 j‖ ^ 2 else 0 := by
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h : i.succ.val ≤ j.val
  · have hj : j ≠ 0 := by
      rintro rfl
      simp at h
    rw [if_pos h, if_pos h, ins_snd_fst_eq_tailPt_snd_fst_of_ne_zero y z hj]
  · rw [if_neg h, if_neg h]

lemma rhoSq_ins_succ {p m : ℕ} (y : Yp p m) (z : ℂ) (i : Fin (p + 1)) :
    rhoSq (ins y z) i.succ = rhoSq (tailPt y) i.succ := by
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.rhoSq
  rw [Lsq_ins, sumR_ins_succ]
  all_goals rfl

lemma bco_ins_succ {p m : ℕ} (y : Yp p m) (z : ℂ) (i : Fin (p + 1)) :
    bco (ins y z) i.succ = bco (tailPt y) i.succ := by
  have h : (∑ j : Fin (p + 1), if i.succ.val ≤ j.val then (ins y z).2.1 j * star ((ins y z).1 j) else 0) =
      ∑ j : Fin (p + 1), if i.succ.val ≤ j.val then (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y).2.1 j * star ((ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y).1 j) else 0 :=
    sum_ins_succ y z i (fun a b => a * star b)
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.bco
  rw [h]
  all_goals rfl

lemma de_ins_succ {p m : ℕ} (y : Yp p m) (z : ℂ) (i : Fin (p + 1)) :
    de (ins y z) i.succ = de (tailPt y) i.succ := by
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.de
  rw [Lsq_ins, rhoSq_ins_succ, bco_ins_succ]

lemma bco_tail_zero {p m : ℕ} (y : Yp p m) : bco (tailPt y) 0 = bco (tailPt y) 1 := by
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.bco
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  induction j using Fin.cases with
  | zero => simp [ReciprocityTheory.ChartRestriction.DS.Xi.tailPt]
  | succ k => simp

lemma Lsq_ge_one {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : 1 ≤ Lsq x l := by
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.Lsq
  have : 0 ≤ ∑ j : Fin p, (if j.val < l.val then ‖x.1 j‖ ^ 2 else 0) :=
    Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)
  linarith

lemma Lsq_mono {p m : ℕ} (x : Xp p m) {l l' : Fin (p + 1)} (h : l ≤ l') : Lsq x l ≤ Lsq x l' := by
  have h' : l.val ≤ l'.val := Fin.le_iff_val_le_val.mp h
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.Lsq
  have : ∑ j : Fin p, (if j.val < l.val then ‖x.1 j‖ ^ 2 else 0) ≤
      ∑ j : Fin p, (if j.val < l'.val then ‖x.1 j‖ ^ 2 else 0) := by
    apply Finset.sum_le_sum
    intro j _
    by_cases h1 : j.val < l.val
    · have h2 : j.val < l'.val := lt_of_lt_of_le h1 h'
      rw [if_pos h1, if_pos h2]
    · rw [if_neg h1]
      split_ifs <;> positivity
  linarith

lemma rhoSq_ge {p m : ℕ} (x : Xp p m) (l l' : Fin (p + 1)) : Lsq x l' ≤ rhoSq x l := by
  have h1 := Lsq_mono x (Fin.le_last l')
  have h2 : 0 ≤ ∑ i, ‖x.2.2.1 i‖ ^ 2 := Finset.sum_nonneg (fun i _ => by positivity)
  have h3 : 0 ≤ ∑ j : Fin p, (if l.val ≤ j.val then ‖x.2.1 j‖ ^ 2 else 0) :=
    Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.rhoSq
  linarith

lemma de_ge_one {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : 1 ≤ de x l := by
  have hL := Lsq_ge_one x l
  have hR : 1 ≤ ReciprocityTheory.ChartRestriction.DS.Xi.rhoSq x l := le_trans hL (rhoSq_ge x l l)
  have hc : 0 ≤ ‖ReciprocityTheory.ChartRestriction.DS.Xi.bco x l‖ ^ 2 := by positivity
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.de
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith)

lemma bco_eq {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) :
    bco x l = (((-(∑ i, ‖x.2.2.1 i‖ ^ 2) / 2 : ℝ)) : ℂ) + (x.2.2.2 : ℂ) * Complex.I - bS x l := rfl

lemma de_sq {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) :
    de x l ^ 2 = (Lsq x l * rhoSq x l + (-(∑ i, ‖x.2.2.1 i‖ ^ 2) / 2 - (bS x l).re) ^ 2) +
      (x.2.2.2 - (bS x l).im) ^ 2 := by
  have hL := Lsq_ge_one x l
  have hR : 1 ≤ ReciprocityTheory.ChartRestriction.DS.Xi.rhoSq x l := le_trans hL (rhoSq_ge x l l)
  have hpos : 0 ≤ ReciprocityTheory.ChartRestriction.DS.Xi.Lsq x l * ReciprocityTheory.ChartRestriction.DS.Xi.rhoSq x l + ‖ReciprocityTheory.ChartRestriction.DS.Xi.bco x l‖ ^ 2 :=
    add_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
  have hre : (ReciprocityTheory.ChartRestriction.DS.Xi.bco x l).re = -(∑ i, ‖x.2.2.1 i‖ ^ 2) / 2 - (bS x l).re := by
    rw [bco_eq]
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have him : (ReciprocityTheory.ChartRestriction.DS.Xi.bco x l).im = x.2.2.2 - (bS x l).im := by
    rw [bco_eq]
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.de
  rw [Real.sq_sqrt hpos, Complex.sq_norm, Complex.normSq_apply, hre, him]
  ring

lemma im_bco {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : (bco x l).im = x.2.2.2 - (bS x l).im := by
  rw [bco_eq]
  simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

def splitE (p m : ℕ) : Xp (p + 1) m ≃ᵐ Yp p m × ℂ :=
  ((MeasurableEquiv.refl (Fin (p + 1) → ℂ)).prodCongr
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (p + 1) => ℂ) 0).prodCongr
        (MeasurableEquiv.refl ((Fin m → ℂ) × ℝ)))).trans
    (((MeasurableEquiv.refl (Fin (p + 1) → ℂ)).prodCongr MeasurableEquiv.prodAssoc).trans
      (MeasurableEquiv.prodAssoc.symm.trans
        ((MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl _)).trans
          (MeasurableEquiv.prodAssoc.trans MeasurableEquiv.prodComm))))

lemma splitE_mp (p m : ℕ) : MeasurePreserving (splitE p m) volume volume := by
  have e1 : MeasurePreserving ((MeasurableEquiv.refl (Fin (p + 1) → ℂ)).prodCongr
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (p + 1) => ℂ) 0).prodCongr
        (MeasurableEquiv.refl ((Fin m → ℂ) × ℝ)))) volume volume :=
    (MeasurePreserving.id volume).prod
      ((volume_preserving_piFinSuccAbove (fun _ : Fin (p + 1) => ℂ) 0).prod (MeasurePreserving.id volume))
  have e2 : MeasurePreserving ((MeasurableEquiv.refl (Fin (p + 1) → ℂ)).prodCongr
      (MeasurableEquiv.prodAssoc :
        (ℂ × (Fin p → ℂ)) × ((Fin m → ℂ) × ℝ) ≃ᵐ ℂ × (Fin p → ℂ) × ((Fin m → ℂ) × ℝ))) volume volume :=
    (MeasurePreserving.id volume).prod volume_preserving_prodAssoc
  have e3 : MeasurePreserving (MeasurableEquiv.prodAssoc :
      ((Fin (p + 1) → ℂ) × ℂ) × ((Fin p → ℂ) × ((Fin m → ℂ) × ℝ)) ≃ᵐ
        (Fin (p + 1) → ℂ) × ℂ × ((Fin p → ℂ) × ((Fin m → ℂ) × ℝ))).symm volume volume :=
    MeasurePreserving.symm _ volume_preserving_prodAssoc
  have e4 : MeasurePreserving ((MeasurableEquiv.prodComm :
      (Fin (p + 1) → ℂ) × ℂ ≃ᵐ ℂ × (Fin (p + 1) → ℂ)).prodCongr
      (MeasurableEquiv.refl ((Fin p → ℂ) × ((Fin m → ℂ) × ℝ)))) volume volume :=
    Measure.measurePreserving_swap.prod (MeasurePreserving.id volume)
  have e5 : MeasurePreserving (MeasurableEquiv.prodAssoc :
      (ℂ × (Fin (p + 1) → ℂ)) × ((Fin p → ℂ) × ((Fin m → ℂ) × ℝ)) ≃ᵐ
        ℂ × (Fin (p + 1) → ℂ) × ((Fin p → ℂ) × ((Fin m → ℂ) × ℝ))) volume volume :=
    volume_preserving_prodAssoc
  have e6 : MeasurePreserving (MeasurableEquiv.prodComm :
      ℂ × ((Fin (p + 1) → ℂ) × ((Fin p → ℂ) × ((Fin m → ℂ) × ℝ))) ≃ᵐ
        ((Fin (p + 1) → ℂ) × ((Fin p → ℂ) × ((Fin m → ℂ) × ℝ))) × ℂ) volume volume :=
    Measure.measurePreserving_swap
  exact e6.comp (e5.comp (e4.comp (e3.comp (e2.comp e1))))

lemma ins_splitE {p m : ℕ} (x : Xp (p + 1) m) : ins (splitE p m x).1 (splitE p m x).2 = x := by
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  funext j
  induction j using Fin.cases with
  | zero => rfl
  | succ k =>
    show x.2.1 (Fin.succAbove 0 k) = x.2.1 k.succ
    simp

lemma split_le {p m : ℕ} (G : Xp (p + 1) m → ℝ≥0∞) :
    ∫⁻ x, G x ≤ ∫⁻ y : Yp p m, ∫⁻ z : ℂ, G (ins y z) := by
  have h := (splitE_mp p m).lintegral_comp_emb (splitE p m).measurableEmbedding
    (fun w => G (ins w.1 w.2))
  simp only [ins_splitE] at h
  exact h.trans_le (lintegral_prod_le _)

lemma cont_Lsq {p m : ℕ} (l : Fin (p + 1)) : Continuous (fun x : Xp p m => Lsq x l) := by
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.Lsq
  exact continuous_const.add (continuous_finsetSum _ (fun j _ => by
    by_cases h : j.val < l.val <;> simp only [h, ↓reduceIte] <;> fun_prop))

lemma cont_rhoSq {p m : ℕ} (l : Fin (p + 1)) : Continuous (fun x : Xp p m => rhoSq x l) := by
  have h1 := cont_Lsq (p := p) (m := m) (Fin.last p)
  have h2 : Continuous fun x : ReciprocityTheory.ChartRestriction.DS.Xi.Xp p m => ∑ i, ‖x.2.2.1 i‖ ^ 2 :=
    continuous_finsetSum _ (fun i _ => by fun_prop)
  have h3 : Continuous fun x : ReciprocityTheory.ChartRestriction.DS.Xi.Xp p m => ∑ j : Fin p, if l.val ≤ j.val then ‖x.2.1 j‖ ^ 2 else 0 :=
    continuous_finsetSum _ (fun j _ => by
      by_cases h : l.val ≤ j.val <;> simp only [h, ↓reduceIte] <;> fun_prop)
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.rhoSq
  exact (h1.add h2).add h3

lemma cont_bco {p m : ℕ} (l : Fin (p + 1)) : Continuous (fun x : Xp p m => bco x l) := by
  have h00 : Continuous fun x : ReciprocityTheory.ChartRestriction.DS.Xi.Xp p m => ∑ i, ‖x.2.2.1 i‖ ^ 2 :=
    continuous_finsetSum _ (fun i _ => by fun_prop)
  have h0 : Continuous fun x : ReciprocityTheory.ChartRestriction.DS.Xi.Xp p m =>
      (((-(∑ i, ‖x.2.2.1 i‖ ^ 2) / 2 : ℝ)) : ℂ) + (x.2.2.2 : ℂ) * Complex.I :=
    (Complex.continuous_ofReal.comp (h00.neg.div_const 2)).add
      ((Complex.continuous_ofReal.comp (by fun_prop : Continuous fun x : ReciprocityTheory.ChartRestriction.DS.Xi.Xp p m => x.2.2.2)).mul continuous_const)
  have hs : Continuous fun x : ReciprocityTheory.ChartRestriction.DS.Xi.Xp p m => ∑ j : Fin p, if l.val ≤ j.val then x.2.1 j * star (x.1 j) else 0 :=
    continuous_finsetSum _ (fun j _ => by
      by_cases h : l.val ≤ j.val <;> simp only [h, ↓reduceIte] <;> fun_prop)
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.bco
  exact h0.sub hs

lemma cont_de {p m : ℕ} (l : Fin (p + 1)) : Continuous (fun x : Xp p m => de x l) := by
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.de
  exact Real.continuous_sqrt.comp
    (((cont_Lsq l).mul (cont_rhoSq l)).add ((cont_bco l).norm.pow 2))

lemma cont_linF {p m : ℕ} (η η' : Fin p → ℂ) (ζ : Fin m → ℂ) : Continuous (linF η η' ζ) := by
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.linF
  exact (continuous_finsetSum _ fun j _ => by fun_prop).add (continuous_finsetSum _ fun i _ => by fun_prop)

lemma cont_tailPt {p m : ℕ} : Continuous (fun y : Yp p m => tailPt y) := by
  have hmid : Continuous fun y : Yp p m => (Fin.cons (0 : ℂ) y.2.1 : Fin (p + 1) → ℂ) :=
    continuous_pi (fun j => by
      induction j using Fin.cases with
      | zero => simp only [Fin.cons_zero]; exact continuous_const
      | succ k => simp only [Fin.cons_succ]; fun_prop)
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.tailPt
  fun_prop

lemma meas_fS {p m : ℕ} (s : Fin (p + 2) → ℝ) : Measurable (fS (p := p) (m := m) s) := by
  unfold fS
  exact Finset.measurable_prod _ (fun l _ =>
    ENNReal.measurable_ofReal.comp ((cont_de (p := p + 1) (m := m) l).measurable.pow_const _))

end OSAux
end ReciprocityTheory.ChartRestriction.DS.Xi
