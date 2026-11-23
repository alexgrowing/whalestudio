import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceLevelSetSmooth
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StStokesOnChart
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLogNormGradDensNonneg
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StMaDensChain
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartMassCompact
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceMassFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceIdeal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceSectionMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PChartMassCompact
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffBoundaryBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceCutChain
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffDominated
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffGradient
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StokesOffDiscriminantWindow
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.LogIntegrableOnOfLogIntegrable
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.SliceCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff

noncomputable section

namespace SliceLevelSetSmooth

def prim (ψ : ℝ → ℝ) (c u : ℝ) : ℝ := ∫ r in c..u, ψ r

def pot (ψ : ℝ → ℝ) (c u : ℝ) : ℝ := ∫ r in c..u, prim ψ c r

variable {ψ : ℝ → ℝ}

theorem hasDerivAt_prim (hψ : Continuous ψ) (c u : ℝ) : HasDerivAt (prim ψ c) (ψ u) u :=
  (hψ.integral_hasStrictDerivAt c u).hasDerivAt

theorem continuous_prim (hψ : Continuous ψ) (c : ℝ) : Continuous (prim ψ c) :=
  continuous_iff_continuousAt.2 fun u => (hasDerivAt_prim hψ c u).continuousAt

theorem deriv_prim (hψ : Continuous ψ) (c : ℝ) : deriv (prim ψ c) = ψ :=
  funext fun u => (hasDerivAt_prim hψ c u).deriv

theorem hasDerivAt_pot (hψ : Continuous ψ) (c u : ℝ) : HasDerivAt (pot ψ c) (prim ψ c u) u :=
  ((continuous_prim hψ c).integral_hasStrictDerivAt c u).hasDerivAt

theorem deriv_pot (hψ : Continuous ψ) (c : ℝ) : deriv (pot ψ c) = prim ψ c :=
  funext fun u => (hasDerivAt_pot hψ c u).deriv

theorem contDiff_prim (hψ : ContDiff ℝ ∞ ψ) (c : ℝ) : ContDiff ℝ ∞ (prim ψ c) :=
  contDiff_infty_iff_deriv.2 ⟨fun u => (hasDerivAt_prim hψ.continuous c u).differentiableAt, by
    rw [deriv_prim hψ.continuous]; exact hψ⟩

theorem contDiff_pot (hψ : ContDiff ℝ ∞ ψ) (c : ℝ) : ContDiff ℝ ∞ (pot ψ c) :=
  contDiff_infty_iff_deriv.2 ⟨fun u => (hasDerivAt_pot hψ.continuous c u).differentiableAt, by
    rw [deriv_pot hψ.continuous]; exact contDiff_prim hψ c⟩

theorem prim_eq_zero {c : ℝ} (hψz : ∀ r, c ≤ r → ψ r = 0) {u : ℝ} (hu : c ≤ u) : prim ψ c u = 0 := by
  have hEq : Set.EqOn ψ (fun _ => (0 : ℝ)) (Set.uIcc c u) := fun r hr => by
    rw [Set.uIcc_of_le hu] at hr
    exact hψz r hr.1
  unfold prim
  rw [intervalIntegral.integral_congr hEq]
  simp

theorem pot_eq_zero {c : ℝ} (hψz : ∀ r, c ≤ r → ψ r = 0) {u : ℝ} (hu : c ≤ u) : pot ψ c u = 0 := by
  have hEq : Set.EqOn (prim ψ c) (fun _ => (0 : ℝ)) (Set.uIcc c u) := fun r hr => by
    rw [Set.uIcc_of_le hu] at hr
    exact prim_eq_zero hψz hr.1
  unfold pot
  rw [intervalIntegral.integral_congr hEq]
  simp

theorem abs_prim_le (hint : Integrable ψ) (c u : ℝ) : |prim ψ c u| ≤ ∫ r, |ψ r| := by
  unfold prim
  rw [← Real.norm_eq_abs, intervalIntegral.norm_integral_eq_norm_integral_uIoc]
  refine (norm_integral_le_integral_norm _).trans ?_
  simp only [Real.norm_eq_abs]
  exact setIntegral_le_integral hint.abs (Eventually.of_forall fun _ => abs_nonneg _)

theorem maDens_cons_const {D : ℕ} (a : ℝ) (φ : Fin D → (Fin (D + 1) → ℂ) → ℝ) (y : Fin (D + 1) → ℂ) :
    maDens (Fin.cons (fun _ => a) φ) y = 0 := by
  have hH : hessC (fun _ : Fin (D + 1) → ℂ => a) y = 0 := by
    ext i j
    simp [hessC]
  unfold maDens
  rw [ChartMassCompact.mdisc_coord_zero _ 0 (by simpa using hH)]
  simp

section Sheets

variable {n e : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin (e + 1)) (Fin n) ℂ}

theorem sheet_eq (hchain : MaDensChain.Statement) {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (L : (Fin n → ℂ) → ℝ)
    (hL : SmoothNear (zeroSet I) L) {x : Fin n → ℂ} {y : Fin (e + 1) → ℂ}
    {s : (Fin (e + 1) → ℂ) → Fin n → ℂ} (hx : x ∈ fibre I A y) (hs : IsSheetAt I A x s) :
    maDens (fun k => (vecCons (F ∘ L) fun _ => L : Fin (e + 1) → (Fin n → ℂ) → ℝ) k ∘ s) y =
      deriv F (L x) * maDens (fun k => (fun _ => L : Fin (e + 1) → (Fin n → ℂ) → ℝ) k ∘ s) y +
        deriv (deriv F) (L x) * gradDens (fun _ : Fin e => L ∘ s) (L ∘ s) (L ∘ s) y := by
  obtain ⟨-, rfl⟩ := hx
  have hsx : s (A *ᵥ x) = x := hs.choose_spec.2.2.2.1
  have hG : ContDiffAt ℝ 2 (L ∘ s) (A *ᵥ x) := StokesOffDiscriminant.contDiffAt_comp_sheet hL hs
  have hcons : (fun k => (fun _ => L : Fin (e + 1) → (Fin n → ℂ) → ℝ) k ∘ s) =
      Fin.cons (L ∘ s) (fun _ : Fin e => L ∘ s) := by
    funext k
    exact Fin.cases rfl (fun _ => rfl) k
  have hch := (hchain e (fun _ => L ∘ s) F (L ∘ s) (A *ᵥ x) hF hG).1
  have hLx : (L ∘ s) (A *ᵥ x) = L x := by simp [hsx]
  rw [hLx] at hch
  rw [vecCons_comp, hcons]
  exact hch

end Sheets

theorem core {n e : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin (e + 1)) (Fin n) ℂ}
    (hS : StokesOnChart.Statement) (hchain : MaDensChain.Statement) (hCM : ChartMassCompact.Statement)
    (hI : I.IsPrime) (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) = (e + 1 : ℕ))
    (hA : IsFiniteProjection I A) (L : (Fin n → ℂ) → ℝ) (hL : SmoothNear (zeroSet I) L)
    (hLK : ∀ c : ℝ, ∃ K : Set (Fin n → ℂ), IsCompact K ∧ ∀ x ∉ K, c < L x)
    (hpos : ∀ y x s, x ∈ fibre I A y → IsSheetAt I A x s →
      0 ≤ gradDens (fun _ : Fin e => L ∘ s) (L ∘ s) (L ∘ s) y)
    (hMint : Integrable (chartAbsDens I A (fun _ => 1) (fun _ => L)))
    (ψ : ℝ → ℝ) (hψs : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψ0 : ∀ r, 0 ≤ ψ r) :
    Integrable (fun y => sheetSum I A (fun x s =>
        |ψ (L x) * gradDens (fun _ : Fin e => L ∘ s) (L ∘ s) (L ∘ s) y|) y) ∧
      (∫ y, sheetSum I A (fun x s =>
        |ψ (L x) * gradDens (fun _ : Fin e => L ∘ s) (L ∘ s) (L ∘ s) y|) y) ≤
        (∫ y, chartAbsDens I A (fun _ => 1) (fun _ => L) y) * ∫ r, |ψ r| := by
  have hψcont := hψs.continuous
  have hψint : Integrable ψ := hψcont.integrable_of_hasCompactSupport hψc
  obtain ⟨b, hb⟩ := hψc.isCompact.bddAbove
  have hψz : ∀ r, b + 1 ≤ r → ψ r = 0 := fun r hr =>
    image_eq_zero_of_notMem_tsupport fun hmem => by linarith [hb hmem]
  obtain ⟨U, hU, hSU, hLU⟩ := hL
  have hLc : ContinuousOn L (zeroSet I) := hLU.continuousOn.mono hSU
  have hΦ : ContDiff ℝ ∞ (pot ψ (b + 1)) := contDiff_pot hψs (b + 1)
  have hΦ2 : ContDiff ℝ 2 (pot ψ (b + 1)) := hΦ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hf : SmoothNear (zeroSet I) (pot ψ (b + 1) ∘ L) := ⟨U, hU, hSU, hΦ.comp_contDiffOn hLU⟩
  have hfc : HasCompactSupport (pot ψ (b + 1) ∘ L) := by
    obtain ⟨K, hK, hKL⟩ := hLK (b + 1)
    exact HasCompactSupport.intro hK fun x hx => pot_eq_zero hψz (hKL x hx).le
  have hsm : ∀ i, SmoothNear (zeroSet I) ((fun _ => L : Fin e → (Fin n → ℂ) → ℝ) i) :=
    fun _ => ⟨U, hU, hSU, hLU⟩
  have hsm' : ∀ i, SmoothNear (zeroSet I)
      ((vecCons (pot ψ (b + 1) ∘ L) fun _ => L : Fin (e + 1) → (Fin n → ℂ) → ℝ) i) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hf
    · exact ⟨U, hU, hSU, hLU⟩
  have hfin : ∀ y, (fibre I A y).Finite := fun y => IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y

  have ha : Integrable (chartDens I A (fun _ => 1) (vecCons (pot ψ (b + 1) ∘ L) fun _ => L)) :=
    CutOffBoundaryBound.integrable_chartDens hCM hI hdim hA continuousOn_const hsm' (Or.inr ⟨0, hfc⟩)

  have hPc : ContinuousOn (prim ψ (b + 1) ∘ L) (zeroSet I) :=
    (continuous_prim hψcont (b + 1)).comp_continuousOn hLc
  have hbm : Measurable (chartDens I A (prim ψ (b + 1) ∘ L) fun _ => L) :=
    CutOffBoundaryBound.measurable_chartDens hI hdim hA hPc fun _ => ⟨U, hU, hSU, hLU⟩
  have hbpt : ∀ y, |chartDens I A (prim ψ (b + 1) ∘ L) (fun _ => L) y| ≤
      (∫ r, |ψ r|) * chartAbsDens I A (fun _ => 1) (fun _ => L) y := by
    intro y
    have hle := SliceCutChain.abs_chartDens_le_add hfin (prim ψ (b + 1) ∘ L) (fun _ => 0) (fun _ => 1)
      (fun _ => L) (∫ r, |ψ r|) (fun y x _ s _ => by
        simp only [Function.comp_apply, zero_mul, abs_zero, one_mul, zero_add, abs_mul]
        exact mul_le_mul_of_nonneg_right (abs_prim_le hψint _ _) (abs_nonneg _)) y
    have h0 : chartAbsDens I A (fun _ => (0 : ℝ)) (fun _ => L) y = 0 := by
      simp [chartAbsDens, sheetSum]
    rwa [h0, zero_add] at hle
  have hbi : Integrable (chartDens I A (prim ψ (b + 1) ∘ L) fun _ => L) :=
    (hMint.const_mul _).mono' hbm.aestronglyMeasurable (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hbpt y)

  have hpt : ∀ y, sheetSum I A (fun x s =>
        |ψ (L x) * gradDens (fun _ : Fin e => L ∘ s) (L ∘ s) (L ∘ s) y|) y =
      chartDens I A (fun _ => 1) (vecCons (pot ψ (b + 1) ∘ L) fun _ => L) y -
        chartDens I A (prim ψ (b + 1) ∘ L) (fun _ => L) y := by
    intro y
    have hc := SliceCutChain.sheetSum_combo (hfin y) 1 0
      (fun x s => (fun _ => (1 : ℝ)) x *
        maDens (fun k => (vecCons (pot ψ (b + 1) ∘ L) fun _ => L : Fin (e + 1) → (Fin n → ℂ) → ℝ) k ∘ s) y)
      (fun x s => (prim ψ (b + 1) ∘ L) x *
        maDens (fun k => (fun _ => L : Fin (e + 1) → (Fin n → ℂ) → ℝ) k ∘ s) y)
      (fun x s => |ψ (L x) * gradDens (fun _ : Fin e => L ∘ s) (L ∘ s) (L ∘ s) y|)
      (fun _ _ => 0) (fun _ _ => 0) (fun x hx s hs => by
        beta_reduce
        rw [sheet_eq hchain hΦ2 L ⟨U, hU, hSU, hLU⟩ hx hs, deriv_pot hψcont, deriv_prim hψcont,
          abs_of_nonneg (mul_nonneg (hψ0 _) (hpos y x s hx hs))]
        simp only [Function.comp_apply]
        ring)
    unfold chartDens
    linarith [hc]

  have hStk := hS n e I A (pot ψ (b + 1) ∘ L) (fun _ => 1) (fun _ => L) hI hdim hA hf
    (smoothNear_of_contDiff contDiff_const) hsm (Or.inl hfc)
  have hzero : chartInt I A (pot ψ (b + 1) ∘ L) (vecCons (fun _ => 1) fun _ => L) = 0 := by
    have h0 : chartDens I A (pot ψ (b + 1) ∘ L) (vecCons (fun _ => 1) fun _ => L) = fun _ => 0 := by
      funext y
      unfold chartDens
      rw [CutOffDominated.sheetSum_eq_sum _ (hfin y)]
      refine Finset.sum_eq_zero fun x _ => ?_
      split_ifs with hs
      · rw [vecCons_comp]
        exact mul_eq_zero_of_right _ (maDens_cons_const 1 _ _)
      · rfl
    unfold chartInt
    rw [h0, integral_zero]
  have haint : ∫ y, chartDens I A (fun _ => 1) (vecCons (pot ψ (b + 1) ∘ L) fun _ => L) y = 0 := by
    have := hStk.symm.trans hzero
    exact this
  refine ⟨(ha.sub hbi).congr (Eventually.of_forall fun y => by
    simp only [Pi.sub_apply]; exact (hpt y).symm), ?_⟩
  have hT : (∫ y, sheetSum I A (fun x s =>
        |ψ (L x) * gradDens (fun _ : Fin e => L ∘ s) (L ∘ s) (L ∘ s) y|) y) =
      ∫ y, (chartDens I A (fun _ => 1) (vecCons (pot ψ (b + 1) ∘ L) fun _ => L) y -
        chartDens I A (prim ψ (b + 1) ∘ L) (fun _ => L) y) :=
    integral_congr_ae (Eventually.of_forall hpt)
  rw [hT, integral_sub ha hbi, haint, zero_sub, ← integral_neg]
  calc (∫ y, -chartDens I A (prim ψ (b + 1) ∘ L) (fun _ => L) y)
      ≤ ∫ y, (∫ r, |ψ r|) * chartAbsDens I A (fun _ => 1) (fun _ => L) y :=
        integral_mono hbi.neg (hMint.const_mul _) fun y => (neg_le_abs _).trans (hbpt y)
    _ = (∫ y, chartAbsDens I A (fun _ => 1) (fun _ => L) y) * ∫ r, |ψ r| := by
        rw [integral_const_mul, mul_comm]

end SliceLevelSetSmooth

theorem SliceLevelSetSmooth.proof (h₁ : StokesOnChart.Statement) (h₂ : LogNormGradDensNonneg.Statement)
    (h₃ : MaDensChain.Statement) (h₄ : ChartMassCompact.Statement) (h₅ : SliceMassFinite.Statement) :
    SliceLevelSetSmooth.Statement := by
  intro n e h W g ℓ A ψ hW hg hℓ hA hψs hψc hψ0
  obtain ⟨hIp, hIdim, -⟩ := SliceIdeal.proof n (e + 1) W g ℓ hW hg hℓ
  have hMint := h₅ n (e + 1) h (W ⊔ Ideal.span {linForm ℓ - 1}) ℓ A hIp
    (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) hIdim hA
  have hslice0 : ∀ x ∈ zeroSet (W ⊔ Ideal.span {linForm ℓ - 1}), x ≠ 0 := by
    intro x hx hx0
    have := hx _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    subst hx0
    simp [linForm] at this
  have hLK : ∀ c : ℝ, ∃ K : Set (Fin n → ℂ), IsCompact K ∧ ∀ x ∉ K, c < Real.log (h.dualNorm x) :=
    fun c => ⟨_, SliceCut.isCompact_sublevel h (Real.exp c), fun x hx => by
      have hx' : Real.exp c < h.dualNorm x := lt_of_not_ge hx
      exact (Real.lt_log_iff_exp_lt ((Real.exp_pos c).trans hx')).2 hx'⟩
  have hpos : ∀ y x s, x ∈ fibre (W ⊔ Ideal.span {linForm ℓ - 1}) A y →
      IsSheetAt (W ⊔ Ideal.span {linForm ℓ - 1}) A x s →
      0 ≤ gradDens (fun _ : Fin e => (fun x => Real.log (h.dualNorm x)) ∘ s)
        ((fun x => Real.log (h.dualNorm x)) ∘ s) ((fun x => Real.log (h.dualNorm x)) ∘ s) y := by
    intro y x s hx hs
    obtain ⟨hxZ, rfl⟩ := hx
    refine h₂ n e h s (A *ᵥ x) _ (CutOffBoundaryBound.analyticAt_of_isSheetAt hs) ?_
    rw [hs.choose_spec.2.2.2.1]
    exact hslice0 x hxZ
  exact SliceLevelSetSmooth.core h₁ h₃ h₄ hIp hIdim hA _ (smoothNear_log_dualNorm_slice h W ℓ) hLK hpos hMint
    ψ hψs hψc hψ0

end

end GroundTheory.Heights₂.Heights
