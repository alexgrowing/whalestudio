import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceRegMassContinuous
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceCutOffLimit
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceMassFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSheetFormCompare
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceIdeal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceCutChain
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffDominated
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.GraphChartEventuallyEqSheet
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.LogIntegrableOnOfLogIntegrable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

namespace SliceRegMassContinuous

variable {n : ℕ}

def fsSq (h : HermNorm n) (u : Fin n → ℂ) (x : Fin n → ℂ) : ℝ :=
  ‖∑ j, u j * x j‖ ^ 2 / h.dualNorm x ^ 2

theorem fsSq_nonneg (h : HermNorm n) (u x : Fin n → ℂ) : 0 ≤ fsSq h u x := by
  unfold fsSq; positivity

theorem fsSq_smul (h : HermNorm n) (u : Fin n → ℂ) (t : ℂ) (x : Fin n → ℂ) (ht : t ≠ 0) :
    fsSq h u (t • x) = fsSq h u x := by
  have hs : ∑ j, u j * (t • x) j = t * ∑ j, u j * x j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
  have ht2 : ‖t‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr ht)
  unfold fsSq
  rw [hs, h.dualNorm_smul, norm_mul, mul_pow, mul_pow, mul_div_mul_left _ _ ht2]

theorem contDiffOn_fsSq (h : HermNorm n) (u : Fin n → ℂ) : ContDiffOn ℝ ∞ (fsSq h u) {x | x ≠ 0} :=
  ((contDiff_norm_sq ℝ).comp (ContDiff.sum fun j _ => contDiff_const.mul (contDiff_apply ℝ ℂ j))).contDiffOn.div
    h.contDiff_dualNorm_sq.contDiffOn fun _ hx => (pow_pos (h.dualNorm_pos hx) 2).ne'

theorem fsLogReg_eq (h : HermNorm n) (u : Fin n → ℂ) (ε : ℝ) {x : Fin n → ℂ} (hx : x ≠ 0) :
    fsLogReg h u ε x = Real.log (fsSq h u x + ε) / 2 := by
  have hN : h.dualNorm x ^ 2 ≠ 0 := (pow_pos (h.dualNorm_pos hx) 2).ne'
  unfold fsLogReg fsSq
  rw [add_div, mul_div_assoc, div_self hN, mul_one]

def coefA (t ε : ℝ) : ℝ := ((t + ε)⁻¹ + t * ((t + ε) ^ 2)⁻¹) / 2

def coefB (t ε : ℝ) : ℝ := ((t + ε) ^ 2)⁻¹ / 2

theorem coef_bound {t ε δ : ℝ} (ht : 0 ≤ t) (hδ : 0 < δ) (hδε : δ ≤ ε) :
    |coefA t ε| ≤ δ⁻¹ ∧ |coefB t ε| ≤ (δ ^ 2)⁻¹ := by
  have hp : 0 < t + ε := by linarith
  have hi : (t + ε)⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ (by linarith)
  have ha : (t + ε)⁻¹ * (t + ε) = 1 := inv_mul_cancel₀ hp.ne'
  have ha0 : 0 ≤ (t + ε)⁻¹ := inv_nonneg.mpr hp.le
  have hsq : ((t + ε) ^ 2)⁻¹ = (t + ε)⁻¹ ^ 2 := (inv_pow _ _).symm
  have hδi : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
  unfold coefA coefB
  rw [hsq, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity), ← inv_pow]
  constructor
  · nlinarith [mul_nonneg ht ha0]
  · nlinarith [pow_le_pow_left₀ ha0 hi 2]

theorem continuousAt_coef {t ε₀ : ℝ} (ht : 0 ≤ t) (hε₀ : 0 < ε₀) :
    ContinuousAt (coefA t) ε₀ ∧ ContinuousAt (coefB t) ε₀ := by
  have hp : t + ε₀ ≠ 0 := by positivity
  have hp2 : (t + ε₀) ^ 2 ≠ 0 := pow_ne_zero 2 hp
  unfold coefA coefB
  constructor <;> fun_prop (disch := first | exact hp | exact hp2)

theorem maDens_sheet {D : ℕ} (h : HermNorm n) (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε)
    (Φ : Fin D → (Fin (D + 1) → ℂ) → ℝ) {s : (Fin (D + 1) → ℂ) → Fin n → ℂ} {U : Set (Fin (D + 1) → ℂ)}
    {y : Fin (D + 1) → ℂ} (hU : IsOpen U) (hyU : y ∈ U) (hs : DifferentiableOn ℂ s U) (hs0 : s y ≠ 0) :
    ReciprocityTheory.AnForm.maDens (Fin.cons (fsLogReg h u ε ∘ s) Φ) y =
      coefA (fsSq h u (s y)) ε * ReciprocityTheory.AnForm.maDens (Fin.cons (fsSq h u ∘ s) Φ) y -
        coefB (fsSq h u (s y)) ε * ReciprocityTheory.AnForm.maDens (Fin.cons (fun z => fsSq h u (s z) ^ 2 / 2) Φ) y := by
  have hsC : ContDiffAt ℂ 2 s y :=
    (IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_differentiableOn hU hs y hyU).contDiffAt
  have hsc : ContDiffAt ℝ 2 s y := hsC.restrict_scalars ℝ
  have hψ : ContDiffAt ℝ 2 (fsSq h u ∘ s) y :=
    (((contDiffOn_fsSq h u).contDiffAt (isOpen_ne.mem_nhds hs0)).of_le (WithTop.coe_le_coe.mpr le_top)).comp y hsc
  have ht := fsSq_nonneg h u (s y)
  have hρ : ContDiffAt ℝ 2 (fun t : ℝ => Real.log (t + ε) / 2) ((fsSq h u ∘ s) y) :=
    ((Real.contDiffAt_log.mpr (by simp only [Function.comp]; positivity)).comp _
      (contDiffAt_id.add contDiffAt_const)).div_const 2
  have hev : (fsLogReg h u ε ∘ s) =ᶠ[𝓝 y] fun z => Real.log ((fsSq h u ∘ s) z + ε) / 2 := by
    filter_upwards [(hs.continuousOn.continuousAt (hU.mem_nhds hyU)).eventually_ne hs0] with z hz
    exact fsLogReg_eq h u ε hz
  have hd1 : deriv (fun t : ℝ => Real.log (t + ε) / 2) = fun t => (t + ε)⁻¹ / 2 := by
    funext t
    simp [deriv_div_const, deriv_comp_add_const, Real.deriv_log]
  have hd2 : deriv (fun t : ℝ => (t + ε)⁻¹ / 2) (fsSq h u (s y)) = -((fsSq h u (s y) + ε) ^ 2)⁻¹ / 2 := by
    simp [deriv_div_const, deriv_comp_add_const, deriv_inv]
  have hcg : ReciprocityTheory.AnForm.maDens (Fin.cons (fsLogReg h u ε ∘ s) Φ) y =
      ReciprocityTheory.AnForm.maDens (Fin.cons (fun z => Real.log ((fsSq h u ∘ s) z + ε) / 2) Φ) y := by
    refine IndefiniteRowSideFullHecke.ComplexSets.maDens_congr_of_eventuallyEq fun k => ?_
    refine Fin.cases ?_ (fun i => ?_) k
    · exact hev
    · exact EventuallyEq.rfl
  rw [hcg, SliceCutChain.maDens_cons_comp (fun t : ℝ => Real.log (t + ε) / 2) (fsSq h u ∘ s) Φ y hρ hψ, hd1]
  simp only [Function.comp, hd2]
  unfold coefA coefB
  ring

theorem exists_compare (hC : SheetFormCompare.Statement) (h : HermNorm n) (u : Fin n → ℂ) (D : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (s : (Fin (D + 1) → ℂ) → Fin n → ℂ) (U : Set (Fin (D + 1) → ℂ)) (y : Fin (D + 1) → ℂ),
      IsOpen U → y ∈ U → DifferentiableOn ℂ s U → s y ≠ 0 →
        |ReciprocityTheory.AnForm.maDens (Fin.cons (fsSq h u ∘ s) fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) y| ≤
            K * |ReciprocityTheory.AnForm.maDens (fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) y| ∧
          |ReciprocityTheory.AnForm.maDens (Fin.cons (fun z => fsSq h u (s z) ^ 2 / 2)
              fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) y| ≤
            K * |ReciprocityTheory.AnForm.maDens (fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) y| := by
  have key : ∀ q : (Fin n → ℂ) → ℝ, (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → q (t • x) = q x) →
      ContDiffOn ℝ ∞ q {x | x ≠ 0} → ∃ K : ℝ, ∀ (s : (Fin (D + 1) → ℂ) → Fin n → ℂ) (U : Set (Fin (D + 1) → ℂ))
        (y : Fin (D + 1) → ℂ), IsOpen U → y ∈ U → DifferentiableOn ℂ s U → s y ≠ 0 →
        |ReciprocityTheory.AnForm.maDens (Fin.cons (q ∘ s) fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) y| ≤
          |K| * |ReciprocityTheory.AnForm.maDens (fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) y| := by
    intro q hq0 hqc
    obtain ⟨K, hK⟩ := hC n (D + 1) h (Fin.cons 0 fun _ => 1) (Fin.cons q fun _ _ => 0)
      (fun k t x ht => by refine Fin.cases ?_ (fun i => ?_) k; exacts [hq0 t x ht, rfl])
      (fun k => by refine Fin.cases ?_ (fun i => ?_) k; exacts [hqc, contDiffOn_const])
    refine ⟨K, fun s U y hU hyU hs hs0 => ?_⟩
    have hfam : (fun k => (fun x => (Fin.cons 0 fun _ => 1 : Fin (D + 1) → ℝ) k * Real.log (h.dualNorm x) +
        (Fin.cons q fun _ _ => 0 : Fin (D + 1) → (Fin n → ℂ) → ℝ) k x) ∘ s) =
        Fin.cons (q ∘ s) fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s := by
      funext k
      refine Fin.cases ?_ (fun i => ?_) k <;> funext z <;> simp
    have := hK s U y hU hyU hs hs0
    rw [hfam] at this
    exact this.trans ((le_abs_self _).trans (abs_mul _ _).le)
  obtain ⟨K₁, hK₁⟩ := key (fsSq h u) (fsSq_smul h u) (contDiffOn_fsSq h u)
  obtain ⟨K₂, hK₂⟩ := key (fun x => fsSq h u x ^ 2 / 2) (fun t x ht => by simp only [fsSq_smul h u t x ht])
    (((contDiffOn_fsSq h u).pow 2).div_const 2)
  refine ⟨max |K₁| |K₂|, (abs_nonneg _).trans (le_max_left _ _), fun s U y hU hyU hs hs0 => ⟨?_, ?_⟩⟩
  · exact (hK₁ s U y hU hyU hs hs0).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  · exact (hK₂ s U y hU hyU hs hs0).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))

theorem term_bound {D : ℕ} (h : HermNorm n) (u : Fin n → ℂ) {ε δ K C a : ℝ} (hδ : 0 < δ) (hδε : δ ≤ ε)
    (ha : |a| ≤ C) {s : (Fin (D + 1) → ℂ) → Fin n → ℂ} {U : Set (Fin (D + 1) → ℂ)} {y : Fin (D + 1) → ℂ}
    (hU : IsOpen U) (hyU : y ∈ U) (hs : DifferentiableOn ℂ s U) (hs0 : s y ≠ 0)
    (hK : |ReciprocityTheory.AnForm.maDens (Fin.cons (fsSq h u ∘ s) fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) y| ≤
            K * |ReciprocityTheory.AnForm.maDens (fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) y| ∧
          |ReciprocityTheory.AnForm.maDens (Fin.cons (fun z => fsSq h u (s z) ^ 2 / 2)
              fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) y| ≤
            K * |ReciprocityTheory.AnForm.maDens (fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) y|) :
    |a * ReciprocityTheory.AnForm.maDens (Fin.cons (fsLogReg h u ε ∘ s) fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) y| ≤
      C * ((δ⁻¹ + (δ ^ 2)⁻¹) * K) *
        |1 * ReciprocityTheory.AnForm.maDens (fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) y| := by
  rw [maDens_sheet h u (hδ.trans_le hδε) _ hU hyU hs hs0, abs_mul, one_mul]
  obtain ⟨hA, hB⟩ := coef_bound (fsSq_nonneg h u (s y)) hδ hδε
  have hC0 : 0 ≤ C := (abs_nonneg _).trans ha
  set Mω := ReciprocityTheory.AnForm.maDens (fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) y
  set M₁ := ReciprocityTheory.AnForm.maDens (Fin.cons (fsSq h u ∘ s) fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) y
  set M₂ := ReciprocityTheory.AnForm.maDens (Fin.cons (fun z => fsSq h u (s z) ^ 2 / 2)
    fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) y
  have hin : |coefA (fsSq h u (s y)) ε * M₁ - coefB (fsSq h u (s y)) ε * M₂| ≤
      δ⁻¹ * (K * |Mω|) + (δ ^ 2)⁻¹ * (K * |Mω|) := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul]
    exact add_le_add (mul_le_mul hA hK.1 (abs_nonneg _) (by positivity))
      (mul_le_mul hB hK.2 (abs_nonneg _) (by positivity))
  calc |a| * _ ≤ C * (δ⁻¹ * (K * |Mω|) + (δ ^ 2)⁻¹ * (K * |Mω|)) := mul_le_mul ha hin (abs_nonneg _) hC0
    _ = _ := by ring

end SliceRegMassContinuous

theorem SliceRegMassContinuous.proof (hM : SliceMassFinite.Statement) (hC : SheetFormCompare.Statement) :
    SliceRegMassContinuous.Statement := by
  classical
  intro n e h W F u' ℓ w C hW hF hℓ hw hwC
  obtain ⟨hprime, hdim, -⟩ := SliceIdeal.proof n (e + 1) W F ℓ hW hF hℓ
  have hmem : linForm ℓ - 1 ∈ W ⊔ Ideal.span {linForm ℓ - 1} :=
    Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hx0 : ∀ x ∈ zeroSet (W ⊔ Ideal.span {linForm ℓ - 1}), x ≠ 0 := by
    rintro x hx rfl
    have := hx _ hmem
    simp [linForm] at this
  unfold varInt
  split_ifs with hA
  swap
  · exact continuousOn_const
  set A := hA.choose with hAdef
  have hAf : IsFiniteProjection (W ⊔ Ideal.span {linForm ℓ - 1}) A := hA.choose_spec
  have hint := hM n (e + 1) h _ ℓ A hprime hmem hdim hAf
  have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hAf
  obtain ⟨K, -, hK⟩ := SliceRegMassContinuous.exists_compare hC h u' e
  intro ε₀ hε₀
  refine ContinuousAt.continuousWithinAt ?_
  unfold chartInt
  refine continuousAt_of_dominated (bound := fun y => C * (((ε₀ / 2)⁻¹ + ((ε₀ / 2) ^ 2)⁻¹) * K) *
      chartAbsDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun _ => 1) (fun _ x => Real.log (h.dualNorm x)) y)
    (Eventually.of_forall fun ε => (SheetSumMeasurable.measurable_sheetSum hAf (fun a b => a * b)
      (continuous_fst.mul continuous_snd).measurable hw _).aestronglyMeasurable) ?_ (hint.const_mul _) ?_
  · filter_upwards [Ioi_mem_nhds (half_lt_self hε₀)] with ε hε
    refine Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs]
    unfold chartDens chartAbsDens
    rw [CutOffDominated.sheetSum_eq_sum _ (hfin y), CutOffDominated.sheetSum_eq_sum _ (hfin y), Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x hx => ?_)
    rw [Set.Finite.mem_toFinset] at hx
    split_ifs with hs
    · obtain ⟨U, hU, hyU, hsd, hsx, -, -⟩ := hs.choose_spec
      rw [show A *ᵥ x = y from hx.2] at hyU hsx
      have hsy : hs.choose y ≠ 0 := by rw [hsx]; exact hx0 x hx.1
      rw [vecCons_comp]
      exact SliceRegMassContinuous.term_bound h u' (half_pos hε₀) (le_of_lt hε) (hwC x) hU hyU hsd hsy
        (hK _ U y hU hyU hsd hsy)
    · simp
  · refine Eventually.of_forall fun y => ?_
    unfold chartDens
    simp only [CutOffDominated.sheetSum_eq_sum _ (hfin y)]
    refine tendsto_finsetSum _ fun x hx => ?_
    rw [Set.Finite.mem_toFinset] at hx
    by_cases hs : ∃ s, IsSheetAt (W ⊔ Ideal.span {linForm ℓ - 1}) A x s
    · simp only [dif_pos hs]
      obtain ⟨U, hU, hyU, hsd, hsx, -, -⟩ := hs.choose_spec
      rw [show A *ᵥ x = y from hx.2] at hyU hsx
      have hsy : hs.choose y ≠ 0 := by rw [hsx]; exact hx0 x hx.1
      obtain ⟨ha, hb⟩ := SliceRegMassContinuous.continuousAt_coef
        (SliceRegMassContinuous.fsSq_nonneg h u' (hs.choose y)) hε₀
      have hc : ContinuousAt (fun ε => w x *
          (SliceRegMassContinuous.coefA (SliceRegMassContinuous.fsSq h u' (hs.choose y)) ε *
              ReciprocityTheory.AnForm.maDens (Fin.cons (SliceRegMassContinuous.fsSq h u' ∘ hs.choose)
                fun _ => (fun x => Real.log (h.dualNorm x)) ∘ hs.choose) y -
            SliceRegMassContinuous.coefB (SliceRegMassContinuous.fsSq h u' (hs.choose y)) ε *
              ReciprocityTheory.AnForm.maDens (Fin.cons (fun z => SliceRegMassContinuous.fsSq h u' (hs.choose z) ^ 2 / 2)
                fun _ => (fun x => Real.log (h.dualNorm x)) ∘ hs.choose) y)) ε₀ :=
        continuousAt_const.mul ((ha.mul continuousAt_const).sub (hb.mul continuousAt_const))
      show ContinuousAt _ ε₀
      refine hc.congr ?_
      filter_upwards [Ioi_mem_nhds hε₀] with ε hε
      rw [vecCons_comp, SliceRegMassContinuous.maDens_sheet h u' hε _ hU hyU hsd hsy]
    · simp only [dif_neg hs]
      exact tendsto_const_nhds

end

end GroundTheory.Heights₂.Heights
