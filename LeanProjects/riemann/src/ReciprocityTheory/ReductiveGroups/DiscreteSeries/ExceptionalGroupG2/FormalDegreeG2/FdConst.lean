import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.ProdSubLtEqFactorial
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.RhoNSubNab
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.VolUFactProdMulLe
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.TraceMulSelfEqSumEigenvaluesSq
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam

noncomputable section

open Finset Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.G2

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem fdc_ncProd (ε : Fin n → Bool) (f : Fin n → Fin n → ℝ) :
    ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b ∧ ¬ ε a = ε b), f a b =
      ∏ ab : PCoord ε, f ab.1.2 ab.1.1 := by
  have e1 : ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b ∧ ¬ ε a = ε b), f a b =
      ∏ x ∈ univ.filter (fun x : Fin n × Fin n => x.1 < x.2 ∧ ¬ ε x.1 = ε x.2), f x.1 x.2 := by
    rw [Finset.prod_filter, Fintype.prod_prod_type]
    simp_rw [Finset.prod_filter]
  rw [e1, ← Finset.prod_subtype (univ.filter (fun x : Fin n × Fin n => x.2 < x.1 ∧ ε x.1 ≠ ε x.2))
    (fun x => by simp) (fun x : Fin n × Fin n => f x.2 x.1)]
  apply Finset.prod_nbij' Prod.swap Prod.swap
  · rintro ⟨a, b⟩ h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.swap_prod_mk] at h ⊢
    exact ⟨h.1, fun e => h.2 e.symm⟩
  · rintro ⟨a, b⟩ h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.swap_prod_mk] at h ⊢
    exact ⟨h.1, fun e => h.2 e.symm⟩
  · intro x _; rfl
  · intro x _; rfl
  · intro x _; rfl

theorem fdc_vand_split (ε : Fin n → Bool) (μ : Fin n → ℝ) :
    Vand μ = (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b ∧ ε a = ε b), (μ a - μ b)) *
      ∏ ab : PCoord ε, (μ ab.1.2 - μ ab.1.1) := by
  rw [← fdc_ncProd ε (fun a b => μ a - μ b), ← Finset.prod_mul_distrib]
  unfold Vand
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_filter_mul_prod_filter_not (univ.filter (fun b : Fin n => a < b)) (fun b => ε a = ε b),
    Finset.filter_filter, Finset.filter_filter]

theorem pi_weight_at_zero_eq (ε : Fin n → Bool) :
    PiW ε 0 = Real.pi ^ (pOf ε * qOf ε) / ∏ ab : PCoord ε, (((ab.1.1 : ℕ) : ℝ) - ((ab.1.2 : ℕ) : ℝ)) := by
  unfold PiW wab
  simp only [Pi.zero_apply, sub_zero, zero_add]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, card_PCoord]

theorem fdc_ncpos (ε : Fin n → Bool) :
    0 < ∏ ab : PCoord ε, (((ab.1.1 : ℕ) : ℝ) - ((ab.1.2 : ℕ) : ℝ)) := by
  refine Finset.prod_pos fun ab _ => sub_pos.2 ?_
  exact_mod_cast ab.2.1

theorem fdc_tend1 (α k m : ℝ) (hm : 0 < m) :
    Tendsto (fun t : ℕ => (α + (t : ℝ) * m + k) / (α + (t : ℝ) * m)) atTop (𝓝 1) := by
  have h : Tendsto (fun t : ℕ => α + (t : ℝ) * m) atTop atTop :=
    tendsto_atTop_add_const_left _ α (tendsto_natCast_atTop_atTop.atTop_mul_const hm)
  have h2 : Tendsto (fun t : ℕ => k / (α + (t : ℝ) * m)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop h
  have h3 := (tendsto_const_nhds (x := (1 : ℝ))).add h2
  rw [add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [h.eventually_gt_atTop 0] with t ht
  field_simp

theorem fdc_tend2 (α m : ℝ) (hm : 0 < m) :
    Tendsto (fun t : ℕ => (t : ℝ) / (α + (t : ℝ) * m)) atTop (𝓝 (1 / m)) := by
  have h : Tendsto (fun t : ℕ => α + (t : ℝ) * m) atTop atTop :=
    tendsto_atTop_add_const_left _ α (tendsto_natCast_atTop_atTop.atTop_mul_const hm)
  have h3 : Tendsto (fun t : ℕ => α / (t : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h4 := (tendsto_const_nhds (x := (1 : ℝ))).div (h3.add_const m) (by rw [zero_add]; exact hm.ne')
  rw [zero_add] at h4
  refine h4.congr' ?_
  filter_upwards [h.eventually_gt_atTop 0, eventually_gt_atTop 0] with t ht ht0
  have : (0 : ℝ) < t := by exact_mod_cast ht0
  show (1:ℝ) / (α / (t:ℝ) + m) = (t:ℝ) / (α + (t:ℝ) * m)
  rw [div_add' _ _ _ this.ne', one_div_div, mul_comm m]

theorem formal_degree_constant_eq {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : IsHCParam lam) (d : ℕ → ℝ)
    (T : ∀ t : ℕ, KType ε (lowK ε (lamT lam t)))
    (h1 : ∀ t, d t / Vand (lamT lam t) = d 0 / Vand lam) (hd0 : 0 < d 0)
    (hup : Filter.limsup (fun t : ℕ => ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε) *
      (Module.finrank ℂ (T t).V : ℝ) / d t)) Filter.atTop ≤ ENNReal.ofReal (cPQ ε * PiW ε 0))
    (hlow : ENNReal.ofReal (cPQ ε * PiW ε 0) ≤ Filter.liminf (fun t : ℕ => ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε) *
      (Module.finrank ℂ (T t).V : ℝ) / d t)) Filter.atTop) :
    d 0 = dimVlam lam := by
  have hV := vand_pos hlam.1
  have hVt : ∀ t, 0 < Vand (lamT lam t) := fun t => vand_pos (strictAnti_lamT hlam.1 t)
  have hFp : 0 < (∏ i ∈ range (pOf ε), (i.factorial : ℝ)) * ∏ i ∈ range (qOf ε), (i.factorial : ℝ) :=
    mul_pos (volU_factProd_pos _) (volU_factProd_pos _)
  have hP := fdc_ncpos ε
  have hform : ∀ t : ℕ, (t : ℝ) ^ (pOf ε * qOf ε) * (Module.finrank ℂ (T t).V : ℝ) / d t =
      Vand lam / (d 0 * ((∏ i ∈ range (pOf ε), (i.factorial : ℝ)) * ∏ i ∈ range (qOf ε), (i.factorial : ℝ))) *
        (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b ∧ ε a = ε b),
          ((lamT lam t a - lamT lam t b + (nab ε a b : ℝ)) / (lamT lam t a - lamT lam t b))) *
        ∏ ab : PCoord ε, ((t : ℝ) / (lamT lam t ab.1.2 - lamT lam t ab.1.1)) := by
    intro t
    have hsplit := fdc_vand_split ε (lamT lam t)
    have hd : d t = d 0 / Vand lam * Vand (lamT lam t) := by
      have := h1 t; rw [div_eq_iff (hVt t).ne'] at this; exact this
    have hne : Vand (lamT lam t) ≠ 0 := (hVt t).ne'
    rw [hsplit] at hne
    have hQ := left_ne_zero_of_mul hne
    have hPn := right_ne_zero_of_mul hne
    simp only [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, card_PCoord]
    rw [hd, lemma7 (T t), hsplit]
    field_simp
  have hR1 : Tendsto (fun t : ℕ => ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b ∧ ε a = ε b),
      ((lamT lam t a - lamT lam t b + (nab ε a b : ℝ)) / (lamT lam t a - lamT lam t b))) atTop
      (𝓝 (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b ∧ ε a = ε b), (1 : ℝ))) := by
    refine tendsto_finsetProd _ fun a _ => tendsto_finsetProd _ fun b hb => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    simp only [lamT_sub]
    refine fdc_tend1 _ _ _ (sub_pos.2 ?_)
    exact_mod_cast hb.1
  have hR2 : Tendsto (fun t : ℕ => ∏ ab : PCoord ε, ((t : ℝ) / (lamT lam t ab.1.2 - lamT lam t ab.1.1))) atTop
      (𝓝 (∏ ab : PCoord ε, 1 / (((ab.1.1 : ℕ) : ℝ) - ((ab.1.2 : ℕ) : ℝ)))) := by
    refine tendsto_finsetProd _ fun ab _ => ?_
    simp only [lamT_sub]
    refine fdc_tend2 _ _ (sub_pos.2 ?_)
    exact_mod_cast ab.2.1
  have hX := ((tendsto_const_nhds (x := Vand lam / (d 0 * ((∏ i ∈ range (pOf ε), (i.factorial : ℝ)) *
      ∏ i ∈ range (qOf ε), (i.factorial : ℝ))))).mul hR1).mul hR2
  have hval : Vand lam / (d 0 * ((∏ i ∈ range (pOf ε), (i.factorial : ℝ)) * ∏ i ∈ range (qOf ε), (i.factorial : ℝ))) *
        (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b ∧ ε a = ε b), (1 : ℝ)) *
        (∏ ab : PCoord ε, 1 / (((ab.1.1 : ℕ) : ℝ) - ((ab.1.2 : ℕ) : ℝ))) =
      Vand lam / (d 0 * ((∏ i ∈ range (pOf ε), (i.factorial : ℝ)) *
        ∏ i ∈ range (qOf ε), (i.factorial : ℝ))) * (1 / ∏ ab : PCoord ε, (((ab.1.1 : ℕ) : ℝ) - ((ab.1.2 : ℕ) : ℝ))) := by
    simp only [Finset.prod_const_one, mul_one, Finset.prod_div_distrib]
  rw [hval] at hX
  have hX' := hX.congr (fun t => (hform t).symm)
  have hE := ENNReal.tendsto_ofReal hX'
  have e1 := hE.limsup_eq
  have e2 := hE.liminf_eq
  rw [e1] at hup
  rw [e2] at hlow
  have hC : 0 ≤ cPQ ε * PiW ε 0 := by
    rw [pi_weight_at_zero_eq]; unfold cPQ
    have := volU_factProd_pos n
    have := volU_factProd_pos (pOf ε)
    have := volU_factProd_pos (qOf ε)
    positivity
  have hL : 0 ≤ Vand lam / (d 0 * ((∏ i ∈ range (pOf ε), (i.factorial : ℝ)) *
      ∏ i ∈ range (qOf ε), (i.factorial : ℝ))) * (1 / ∏ ab : PCoord ε, (((ab.1.1 : ℕ) : ℝ) - ((ab.1.2 : ℕ) : ℝ))) := by
    positivity
  have heq := (ENNReal.ofReal_eq_ofReal_iff hL hC).1 (le_antisymm hup hlow)
  rw [pi_weight_at_zero_eq] at heq
  unfold cPQ at heq
  have hpi : 0 < Real.pi ^ (pOf ε * qOf ε) := pow_pos Real.pi_pos _
  have hI := volU_factProd_pos n
  rw [dimVlam_eq_vand hlam.1]
  field_simp at heq
  field_simp
  nlinarith [heq]

end ReciprocityTheory.ChartRestriction.DS.G2
