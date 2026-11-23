import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.LintegralInsertFiberLe
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.DeZeroBounds

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace OSAux

theorem avg {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ] (Φ : ℝ → X → X)
    (hΦm : Measurable (fun q : ℝ × X => Φ q.1 q.2))
    (hΦ : ∀ t ∈ Icc (1 : ℝ) 2, MeasurePreserving (Φ t) μ μ) {f w : X → ℝ≥0∞}
    (hf : Measurable f) (hw : Measurable w) (K : ℝ≥0∞)
    (hK : ∀ t ∈ Icc (1 : ℝ) 2, ∀ x, f (Φ t x) ≤ K * f x) :
    ∫⁻ x, f x * w x ∂μ ≤ K * ∫⁻ x, f x * (∫⁻ t in Icc (1 : ℝ) 2, w (Φ t x)) ∂μ := by
  have hvol : volume (Icc (1 : ℝ) 2) = 1 := by
    rw [Real.volume_Icc]; norm_num
  have hm2 : Measurable (fun q : ℝ × X => f q.2 * w (Φ q.1 q.2)) :=
    (hf.comp measurable_snd).mul (hw.comp hΦm)
  have hm3 : Measurable fun t : ℝ => ∫⁻ x, f x * w (Φ t x) ∂μ := hm2.lintegral_prod_right'
  calc ∫⁻ x, f x * w x ∂μ = ∫⁻ _t in Icc (1 : ℝ) 2, (∫⁻ x, f x * w x ∂μ) := by
        rw [setLIntegral_const, hvol, mul_one]
    _ ≤ ∫⁻ t in Icc (1 : ℝ) 2, K * (∫⁻ x, f x * w (Φ t x) ∂μ) := by
        refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
        calc ∫⁻ x, f x * w x ∂μ = ∫⁻ x, f (Φ t x) * w (Φ t x) ∂μ :=
              ((hΦ t ht).lintegral_comp (hf.mul hw)).symm
          _ ≤ ∫⁻ x, K * (f x * w (Φ t x)) ∂μ := lintegral_mono fun x => by
              rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (hK t ht x) zero_le
          _ = K * ∫⁻ x, f x * w (Φ t x) ∂μ :=
              lintegral_const_mul K (hf.mul (hw.comp (hΦ t ht).measurable))
    _ = K * ∫⁻ t in Icc (1 : ℝ) 2, (∫⁻ x, f x * w (Φ t x) ∂μ) := lintegral_const_mul K hm3
    _ = K * ∫⁻ x, (∫⁻ t in Icc (1 : ℝ) 2, f x * w (Φ t x)) ∂μ := by
        rw [lintegral_lintegral_swap (f := fun t x => f x * w (Φ t x)) hm2.aemeasurable]
    _ = K * ∫⁻ x, f x * (∫⁻ t in Icc (1 : ℝ) 2, w (Φ t x)) ∂μ := by
        congr 1
        refine lintegral_congr fun x => ?_
        exact lintegral_const_mul (f x)
          ((show Measurable (Function.uncurry fun t x => w (Φ t x)) from hw.comp hΦm).of_uncurry_right)

lemma exponentCondition_neg {p : ℕ} (e : Fin (p + 2) → ℝ) {α : ℝ} (he : ∀ l, 0 < e l)
    (hα : 2 * ∑ i : Fin (p + 1), e i.succ < α) :
    CHCond p (Function.update (fun i : Fin (p + 1) => -e i.succ) 0
        (α + (fun i : Fin (p + 1) => -e i.succ) 0)) ∧
      0 < α + 2 * ∑ i, (fun i : Fin (p + 1) => -e i.succ) i := by
  have hpos : ∀ i : Fin (p + 1), 0 ≤ e i.succ := fun i => (he _).le
  have hS : ∀ s : Finset (Fin (p + 1)), ∑ i ∈ s, e i.succ ≤ ∑ i : Fin (p + 1), e i.succ :=
    fun s => Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) fun i _ _ => hpos i
  have hN : ∀ s : Finset (Fin (p + 1)), 0 ≤ ∑ i ∈ s, e i.succ :=
    fun s => Finset.sum_nonneg fun i _ => hpos i
  have hupd : ∀ j, Function.update (fun i : Fin (p + 1) => -e i.succ) 0
      (α + (fun i : Fin (p + 1) => -e i.succ) 0) j = -e j.succ + if j = 0 then α else 0 := by
    intro j
    rw [Function.update_apply]
    split_ifs with hj
    · subst hj
      show α + -e (Fin.succ 0) = -e (Fin.succ 0) + α
      ring
    · show -e j.succ = -e j.succ + 0
      ring
  have hsum : ∀ s : Finset (Fin (p + 1)), ∑ j ∈ s, Function.update (fun i : Fin (p + 1) => -e i.succ) 0
      (α + (fun i : Fin (p + 1) => -e i.succ) 0) j =
        -∑ j ∈ s, e j.succ + if (0 : Fin (p + 1)) ∈ s then α else 0 := by
    intro s
    rw [Finset.sum_congr rfl fun j _ => hupd j, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    congr 1
    simp
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.CHCond
  refine ⟨⟨fun l => ?_, fun l _ => ?_⟩, ?_⟩
  · have h0 : (0 : Fin (p + 1)) ∈ Finset.Iic l := by simp
    rw [hsum, if_pos h0]
    linarith [hS (Finset.Iic l), hN Finset.univ]
  · have h0 : (0 : Fin (p + 1)) ∈ Finset.Iic l := by simp
    have h0' : (0 : Fin (p + 1)) ∉ Finset.Ioi l := by simp [Finset.mem_Ioi]
    have hdis : Disjoint (Finset.Iic l) (Finset.Ioi l) :=
      Finset.disjoint_left.2 fun j h1 h2 =>
        lt_irrefl _ (lt_of_le_of_lt (Finset.mem_Iic.1 h1) (Finset.mem_Ioi.1 h2))
    have hAB : ∑ j ∈ Finset.Iic l, e j.succ + ∑ j ∈ Finset.Ioi l, e j.succ ≤
        ∑ j : Fin (p + 1), e j.succ := by
      rw [← Finset.sum_union hdis]; exact hS _
    rw [hsum, hsum, if_pos h0, if_neg h0']
    linarith [hN (Finset.Iic l), hN (Finset.Ioi l)]
  · show 0 < α + 2 * ∑ i : Fin (p + 1), -e i.succ
    rw [Finset.sum_neg_distrib]
    linarith [hN Finset.univ]

private theorem lintegral_prod4_eq_iterated {A B C : Type*} [MeasureSpace A] [MeasureSpace B] [MeasureSpace C]
    [SigmaFinite (volume : Measure A)] [SigmaFinite (volume : Measure B)]
    [SigmaFinite (volume : Measure C)]
    (T : A × B × C × ℝ → ℝ≥0∞) (hT : Measurable T) :
    ∫⁻ y, T y = ∫⁻ a, ∫⁻ b, ∫⁻ c, ∫⁻ t, T (a, b, c, t) := by
  simp only [Measure.volume_eq_prod]
  rw [lintegral_prod _ hT.aemeasurable]
  refine lintegral_congr fun a => ?_
  rw [lintegral_prod (fun w : B × C × ℝ => T (a, w))
    (hT.comp (by fun_prop : Measurable fun w : B × C × ℝ => (a, w))).aemeasurable]
  refine lintegral_congr fun b => ?_
  exact lintegral_prod (fun w : C × ℝ => T (a, b, w))
    (hT.comp (by fun_prop : Measurable fun w : C × ℝ => (a, b, w))).aemeasurable

theorem tail_bound (hT : TailFin) (hC1 : C1) (hK : KER) (hL : SLOW) {p m : ℕ} (e : Fin (p + 2) → ℝ)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (he : ∀ l, 0 < e l)
    (hsum : e 0 + 2 * ∑ i : Fin (p + 1), e i.succ < γ / 2) :
    ∃ C : ℝ, ∫⁻ x : Xp (p + 1) m, fS (fun l => s0N (p + 1) m l - e l) x * (‖x.2.1 0‖₊ : ℝ≥0∞) ^ (-γ) ≤
      ENNReal.ofReal C := by
  have hS0 : 0 ≤ ∑ i : Fin (p + 1), e i.succ := Finset.sum_nonneg fun i _ => (he _).le
  have he0γ : e 0 < γ := by linarith
  have hγ2 : γ < 2 := by linarith
  have hα : 0 < γ / 2 - e 0 := by linarith
  have he1 : ∀ l, e l ≤ 1 := by
    intro l
    rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨i, rfl⟩
    · linarith
    · have : e i.succ ≤ ∑ j : Fin (p + 1), e j.succ :=
        Finset.single_le_sum (f := fun j : Fin (p + 1) => e j.succ) (fun j _ => (he _).le)
          (Finset.mem_univ i)
      linarith [he 0]
  obtain ⟨CK, hCK0, hCK⟩ := lintegral_insertFiber_le hC1 hK (he 0) he0γ hγ2
  obtain ⟨CS, hCS0, hCS⟩ := beta_bound (m := m) hL e he he1 hγ2 hα
  have hec := exponentCondition_neg (α := γ / 2 - e 0) e he (by linarith)
  have hfin := hT p m (γ / 2 - e 0) (fun i => -e i.succ) hec.1 hec.2
  have hc0 : ReciprocityTheory.ChartRestriction.DS.Xi.s0N (p + 1) m 0 = 2 := by simp [ReciprocityTheory.ChartRestriction.DS.Xi.s0N]
  obtain ⟨P, hP⟩ : ∃ P : Yp p m → ℝ≥0∞, P = fun y => ∏ i : Fin (p + 1),
      ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.Xi.de (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y) i.succ ^
        (-(ReciprocityTheory.ChartRestriction.DS.Xi.s0N (p + 1) m i.succ - e i.succ))) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : Yp p m → ℝ≥0∞, F = fun y =>
      ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.Xi.Lsq (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y) 1 ^ (-1 + γ / 2)) *
        ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.Xi.de (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y) 0 ^ (-(γ - e 0))) * P y := ⟨_, rfl⟩
  obtain ⟨T, hTd⟩ : ∃ T : Yp p m → ℝ≥0∞, T = fun y =>
      ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.Xi.Lsq (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y) 1 ^ ((-2 + (γ / 2 - e 0)) / 2)) *
        ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.Xi.de (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y) 1 ^ (-(γ / 2 - e 0))) *
        ∏ i : Fin (p + 1), ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.Xi.de (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y) i.succ ^
          (-(ReciprocityTheory.ChartRestriction.DS.Xi.s0N (p + 1) m i.succ + (fun i : Fin (p + 1) => -e i.succ) i))) := ⟨_, rfl⟩
  have hmL : ∀ l : Fin (p + 1 + 1), Measurable fun y : Yp p m => ReciprocityTheory.ChartRestriction.DS.Xi.Lsq (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y) l :=
    fun l => ((cont_Lsq l).comp cont_tailPt).measurable
  have hmH : ∀ l : Fin (p + 1 + 1), Measurable fun y : Yp p m => ReciprocityTheory.ChartRestriction.DS.Xi.de (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y) l :=
    fun l => ((cont_de l).comp cont_tailPt).measurable
  have hPm : Measurable P := by
    rw [hP]
    exact Finset.measurable_prod _ fun i _ => ENNReal.measurable_ofReal.comp ((hmH i.succ).pow_const _)
  have hFm : Measurable F := by
    rw [hF]
    exact ((ENNReal.measurable_ofReal.comp ((hmL 1).pow_const _)).mul
      (ENNReal.measurable_ofReal.comp ((hmH 0).pow_const _))).mul hPm
  have hTm : Measurable T := by
    rw [hTd]
    exact ((ENNReal.measurable_ofReal.comp ((hmL 1).pow_const _)).mul
      (ENNReal.measurable_ofReal.comp ((hmH 1).pow_const _))).mul
      (Finset.measurable_prod _ fun i _ => ENNReal.measurable_ofReal.comp ((hmH i.succ).pow_const _))
  have hPne : ∀ y, P y ≠ ∞ := fun y => by
    rw [hP]; exact ENNReal.prod_ne_top fun i _ => ENNReal.ofReal_ne_top
  have hinner : ∀ y : Yp p m,
      ∫⁻ z : ℂ, fS (fun l => ReciprocityTheory.ChartRestriction.DS.Xi.s0N (p + 1) m l - e l) (ins y z) *
        (‖(ins y z).2.1 0‖₊ : ℝ≥0∞) ^ (-γ) ≤ ENNReal.ofReal CK * F y := by
    intro y
    have h1 : ∀ z, fS (fun l => ReciprocityTheory.ChartRestriction.DS.Xi.s0N (p + 1) m l - e l) (ins y z) =
        ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.Xi.de (ins y z) 0 ^ (-(ReciprocityTheory.ChartRestriction.DS.Xi.s0N (p + 1) m 0 - e 0))) *
        ∏ i : Fin (p + 1), ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.Xi.de (ins y z) i.succ ^
          (-(ReciprocityTheory.ChartRestriction.DS.Xi.s0N (p + 1) m i.succ - e i.succ))) :=
      fun z => Fin.prod_univ_succ _
    have hz : ∀ z, (ins y z).2.1 0 = z := fun z => by simp [ins]
    have hPz : ∀ z, ∏ i : Fin (p + 1), ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.Xi.de (ins y z) i.succ ^
        (-(ReciprocityTheory.ChartRestriction.DS.Xi.s0N (p + 1) m i.succ - e i.succ))) = P y := fun z => by
      rw [hP]
      exact Finset.prod_congr rfl fun i _ => by rw [de_ins_succ]
    have hnn : 0 ≤ CK * ReciprocityTheory.ChartRestriction.DS.Xi.Lsq (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y) 1 ^ (-1 + γ / 2) :=
      mul_nonneg hCK0.le (Real.rpow_nonneg (zero_le_one.trans (Lsq_ge_one _ _)) _)
    calc ∫⁻ z : ℂ, fS (fun l => ReciprocityTheory.ChartRestriction.DS.Xi.s0N (p + 1) m l - e l) (ins y z) *
          (‖(ins y z).2.1 0‖₊ : ℝ≥0∞) ^ (-γ)
        = ∫⁻ z : ℂ, P y * (ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.Xi.de (ins y z) 0 ^ (-(2 - e 0))) *
            (‖z‖₊ : ℝ≥0∞) ^ (-γ)) := by
          refine lintegral_congr fun z => ?_
          rw [h1 z, hc0, hz z, hPz z]
          ring
      _ = P y * ∫⁻ z : ℂ, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.Xi.de (ins y z) 0 ^ (-(2 - e 0))) *
            (‖z‖₊ : ℝ≥0∞) ^ (-γ) := lintegral_const_mul' _ _ (hPne y)
      _ ≤ P y * ENNReal.ofReal (CK * ReciprocityTheory.ChartRestriction.DS.Xi.Lsq (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y) 1 ^ (-1 + γ / 2) *
            ReciprocityTheory.ChartRestriction.DS.Xi.de (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y) 0 ^ (-(γ - e 0))) := mul_le_mul_of_nonneg_left (hCK y) zero_le
      _ = ENNReal.ofReal CK * F y := by
          simp only [hF]
          rw [ENNReal.ofReal_mul hnn, ENNReal.ofReal_mul hCK0.le]
          ring
  have hkey : ∫⁻ y, F y ≤ ENNReal.ofReal CS * ReciprocityTheory.ChartRestriction.DS.Xi.TailInt p m (γ / 2 - e 0) (fun i => -e i.succ) := by
    have htail : ReciprocityTheory.ChartRestriction.DS.Xi.TailInt p m (γ / 2 - e 0) (fun i => -e i.succ) = ∫⁻ y, T y := by
      rw [hTd]; rfl
    rw [htail, lintegral_prod4_eq_iterated F hFm, lintegral_prod4_eq_iterated T hTm]
    calc ∫⁻ a : Fin (p + 1) → ℂ, ∫⁻ b : Fin p → ℂ, ∫⁻ c : Fin m → ℂ, ∫⁻ t : ℝ, F (a, b, c, t)
        ≤ ∫⁻ a : Fin (p + 1) → ℂ, ∫⁻ b : Fin p → ℂ, ∫⁻ c : Fin m → ℂ,
            ENNReal.ofReal CS * ∫⁻ t : ℝ, T (a, b, c, t) := by
          refine lintegral_mono fun a => lintegral_mono fun b => lintegral_mono fun c => ?_
          subst hF hP hTd
          exact hCS a b c
      _ = ENNReal.ofReal CS * ∫⁻ a : Fin (p + 1) → ℂ, ∫⁻ b : Fin p → ℂ, ∫⁻ c : Fin m → ℂ,
            ∫⁻ t : ℝ, T (a, b, c, t) := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun a => ?_
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun b => ?_
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine ⟨CK * CS * (ReciprocityTheory.ChartRestriction.DS.Xi.TailInt p m (γ / 2 - e 0) (fun i => -e i.succ)).toReal, ?_⟩
  calc _ ≤ ∫⁻ y : Yp p m, ∫⁻ z : ℂ,
        fS (fun l => ReciprocityTheory.ChartRestriction.DS.Xi.s0N (p + 1) m l - e l) (ins y z) *
          (‖(ins y z).2.1 0‖₊ : ℝ≥0∞) ^ (-γ) := split_le _
    _ ≤ ∫⁻ y : Yp p m, ENNReal.ofReal CK * F y := lintegral_mono hinner
    _ = ENNReal.ofReal CK * ∫⁻ y, F y := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal CK * (ENNReal.ofReal CS * ReciprocityTheory.ChartRestriction.DS.Xi.TailInt p m (γ / 2 - e 0) (fun i => -e i.succ)) :=
        mul_le_mul_of_nonneg_left hkey zero_le
    _ = _ := by
        rw [ENNReal.ofReal_mul (mul_nonneg hCK0.le hCS0.le), ENNReal.ofReal_mul hCK0.le,
          ENNReal.ofReal_toReal hfin.ne]
        ring

end OSAux
end ReciprocityTheory.ChartRestriction.DS.Xi
