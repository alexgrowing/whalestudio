import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceCutChain
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartMassCompact
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffBoundaryBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffGradient
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHessCCompPluri
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLogLogCutHessDeriv
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFibreBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceIdeal
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsPiola
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff

noncomputable section

namespace SliceCutChain

theorem hessC_comp {D : ℕ} (ρ : ℝ → ℝ) (ψ : (Fin D → ℂ) → ℝ) (y : Fin D → ℂ)
    (hρ : ContDiffAt ℝ 2 ρ (ψ y)) (hψ : ContDiffAt ℝ 2 ψ y) :
    hessC (fun w => ρ (ψ w)) y =
      ((deriv ρ (ψ y) - deriv (deriv ρ) (ψ y) * ψ y : ℝ) : ℂ) • hessC ψ y +
        ((deriv (deriv ρ) (ψ y) : ℝ) : ℂ) • hessC (fun w => ψ w ^ 2 / 2) y := by
  have hQ : ContDiffAt ℝ 2 (fun t : ℝ => t ^ 2 / 2) (ψ y) :=
    ((contDiff_id.pow 2).div_const 2).contDiffAt
  have hd1 : deriv (fun t : ℝ => t ^ 2 / 2) = fun t => t := by
    funext t
    rw [((hasDerivAt_pow 2 t).div_const 2).deriv]
    norm_num
  have key := HessCCompPluri.fderiv_fderiv_comp_apply hρ hψ
  have keyQ := HessCCompPluri.fderiv_fderiv_comp_apply hQ hψ
  simp only [hd1, deriv_id'', one_mul] at keyQ
  ext i j
  simp only [hessC, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [key, keyQ]
  push_cast
  ring

theorem maDens_cons_comp {D : ℕ} (ρ : ℝ → ℝ) (ψ : (Fin (D + 1) → ℂ) → ℝ)
    (Φ : Fin D → (Fin (D + 1) → ℂ) → ℝ) (y : Fin (D + 1) → ℂ)
    (hρ : ContDiffAt ℝ 2 ρ (ψ y)) (hψ : ContDiffAt ℝ 2 ψ y) :
    maDens (Fin.cons (fun w => ρ (ψ w)) Φ) y =
      deriv ρ (ψ y) * maDens (Fin.cons ψ Φ) y +
        deriv (deriv ρ) (ψ y) *
          (maDens (Fin.cons (fun w => ψ w ^ 2 / 2) Φ) y - ψ y * maDens (Fin.cons ψ Φ) y) := by
  rw [maDens_cons_eq, maDens_cons_eq, maDens_cons_eq, hessC_comp ρ ψ y hρ hψ, mdisc_cons_smul_add,
    Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  ring

theorem deriv_comp_cut (g : ℝ → ℝ) (hg : Differentiable ℝ g) (k : ℕ) :
    deriv (fun r : ℝ => g (2 - r / ((k : ℝ) + 1))) =
      fun r => -((k : ℝ) + 1)⁻¹ * deriv g (2 - r / ((k : ℝ) + 1)) := by
  funext r
  have h1 : HasDerivAt (fun r : ℝ => 2 - r / ((k : ℝ) + 1)) (-(1 / ((k : ℝ) + 1))) r :=
    ((hasDerivAt_id r).div_const ((k : ℝ) + 1)).const_sub 2
  have h2 : HasDerivAt (fun r : ℝ => g (2 - r / ((k : ℝ) + 1)))
      (deriv g (2 - r / ((k : ℝ) + 1)) * (-(1 / ((k : ℝ) + 1)))) r :=
    (hg _).hasDerivAt.comp r h1
  rw [h2.deriv]
  ring

theorem deriv_cut (k : ℕ) (r : ℝ) :
    deriv (fun r : ℝ => Real.smoothTransition (2 - r / ((k : ℝ) + 1))) r =
        -((k : ℝ) + 1)⁻¹ * deriv Real.smoothTransition (2 - r / ((k : ℝ) + 1)) ∧
      deriv (deriv fun r : ℝ => Real.smoothTransition (2 - r / ((k : ℝ) + 1))) r =
        ((k : ℝ) + 1)⁻¹ ^ 2 * deriv (deriv Real.smoothTransition) (2 - r / ((k : ℝ) + 1)) := by
  have hsm : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  obtain ⟨hd0, h1⟩ := contDiff_infty_iff_deriv.1 hsm
  have hd1 : Differentiable ℝ (deriv Real.smoothTransition) := h1.differentiable (by simp)
  refine ⟨congrFun (deriv_comp_cut _ hd0 k) r, ?_⟩
  rw [deriv_comp_cut _ hd0 k]
  have hdiff : DifferentiableAt ℝ (fun r : ℝ => deriv Real.smoothTransition (2 - r / ((k : ℝ) + 1))) r :=
    (hd1 _).comp r ((differentiableAt_id.div_const _).const_sub 2)
  rw [deriv_const_mul _ hdiff, congrFun (deriv_comp_cut _ hd1 k) r]
  ring

theorem sheet_identity {n e : ℕ} (h : HermNorm n) (k : ℕ) (s : (Fin (e + 1) → ℂ) → Fin n → ℂ)
    (y : Fin (e + 1) → ℂ) (hx0 : s y ≠ 0) (hs : ContDiffAt ℝ 2 s y) :
    maDens (fun i => (vecCons (sliceCut h k) fun _ x => Real.log (h.dualNorm x) :
        Fin (e + 1) → (Fin n → ℂ) → ℝ) i ∘ s) y =
      -((k : ℝ) + 1)⁻¹ * deriv Real.smoothTransition (2 - Real.log (h.dualNorm (s y)) / ((k : ℝ) + 1)) *
          maDens (fun i => (fun _ x => Real.log (h.dualNorm x) : Fin (e + 1) → (Fin n → ℂ) → ℝ) i ∘ s) y +
        ((k : ℝ) + 1)⁻¹ ^ 2 *
          deriv (deriv Real.smoothTransition) (2 - Real.log (h.dualNorm (s y)) / ((k : ℝ) + 1)) *
          (maDens (fun i => (vecCons (fun x => Real.log (h.dualNorm x) ^ 2 / 2) fun _ x =>
              Real.log (h.dualNorm x) : Fin (e + 1) → (Fin n → ℂ) → ℝ) i ∘ s) y -
            Real.log (h.dualNorm (s y)) *
              maDens (fun i => (fun _ x => Real.log (h.dualNorm x) : Fin (e + 1) → (Fin n → ℂ) → ℝ) i ∘ s) y) := by
  set ψ : (Fin (e + 1) → ℂ) → ℝ := fun w => Real.log (h.dualNorm (s w)) with hψdef
  have hT : ContDiffAt ℝ 2 (fun x : Fin n → ℂ => Real.log (h.dualNorm x)) (s y) :=
    ((contDiffOn_log_dualNorm h).contDiffAt (isOpen_compl_singleton.mem_nhds hx0)).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hψ : ContDiffAt ℝ 2 ψ y := hT.comp y hs
  have hρ : ContDiffAt ℝ 2 (fun r : ℝ => Real.smoothTransition (2 - r / ((k : ℝ) + 1))) (ψ y) :=
    (Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_id.div_const _))).contDiffAt
  have key := maDens_cons_comp (fun r : ℝ => Real.smoothTransition (2 - r / ((k : ℝ) + 1))) ψ
    (fun _ : Fin e => ψ) y hρ hψ
  obtain ⟨hd1, hd2⟩ := deriv_cut k (ψ y)
  rw [hd1, hd2] at key
  have e1 : (fun i => (vecCons (sliceCut h k) fun _ x => Real.log (h.dualNorm x) :
      Fin (e + 1) → (Fin n → ℂ) → ℝ) i ∘ s) =
      Fin.cons (fun w => Real.smoothTransition (2 - ψ w / ((k : ℝ) + 1))) (fun _ : Fin e => ψ) :=
    vecCons_comp _ _ s
  have e0 : (fun i => (fun _ x => Real.log (h.dualNorm x) : Fin (e + 1) → (Fin n → ℂ) → ℝ) i ∘ s) =
      Fin.cons ψ (fun _ : Fin e => ψ) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  have e2 : (fun i => (vecCons (fun x => Real.log (h.dualNorm x) ^ 2 / 2) fun _ x =>
      Real.log (h.dualNorm x) : Fin (e + 1) → (Fin n → ℂ) → ℝ) i ∘ s) =
      Fin.cons (fun w => ψ w ^ 2 / 2) (fun _ : Fin e => ψ) :=
    vecCons_comp _ _ s
  rw [e1, e0, e2, key]

theorem sheetSum_combo {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {y : Fin d → ℂ} (hfin : (fibre J A y).Finite) (c₁ c₂ : ℝ)
    (F₁ F₂ F₃ F₄ F₅ : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ)
    (h : ∀ x ∈ fibre J A y, ∀ s, IsSheetAt J A x s →
      F₁ x s - F₂ x s = c₁ * F₃ x s + c₂ * (F₄ x s - F₅ x s)) :
    sheetSum J A F₁ y - sheetSum J A F₂ y =
      c₁ * sheetSum J A F₃ y + c₂ * (sheetSum J A F₄ y - sheetSum J A F₅ y) := by
  classical
  unfold sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  split_ifs with hs
  · exact h x hx _ hs.choose_spec
  · ring

theorem abs_chartDens_le_add {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (hfin : ∀ y, (fibre J A y).Finite) (w v₁ v₂ : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (M : ℝ)
    (h : ∀ y, ∀ x ∈ fibre J A y, ∀ s, IsSheetAt J A x s →
      |w x * maDens (fun k => φ k ∘ s) y| ≤
        |v₁ x * maDens (fun k => φ k ∘ s) y| + M * |v₂ x * maDens (fun k => φ k ∘ s) y|)
    (y : Fin d → ℂ) :
    |chartDens J A w φ y| ≤ chartAbsDens J A v₁ φ y + M * chartAbsDens J A v₂ φ y := by
  classical
  refine (abs_chartDens_le J A w φ y).trans ?_
  unfold chartAbsDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y), finsum_mem_eq_finite_toFinset_sum _ (hfin y),
    finsum_mem_eq_finite_toFinset_sum _ (hfin y), Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  split_ifs with hs
  · exact h y x hx _ hs.choose_spec
  · simp

theorem integrable_of_dom {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {w v₁ v₂ : (Fin n → ℂ) → ℝ} {φ : Fin d → (Fin n → ℂ) → ℝ} {M : ℝ}
    (hm : Measurable (chartDens J A w φ)) (h₁ : Integrable (chartAbsDens J A v₁ φ))
    (h₂ : Integrable (chartAbsDens J A v₂ φ))
    (hle : ∀ y, |chartDens J A w φ y| ≤ chartAbsDens J A v₁ φ y + M * chartAbsDens J A v₂ φ y) :
    Integrable (chartDens J A w φ) :=
  (h₁.add (h₂.const_mul M)).mono' hm.aestronglyMeasurable
    (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hle y)

theorem term_dom {X : Type*} (B : Set X) (band : X → Prop) (p q r : X → ℝ) (M m : ℝ) (x : X)
    (h0 : ¬ band x → r x = 0) (hB : band x → x ∈ B) (hr : band x → |r x| ≤ M) (hM : 0 ≤ M) :
    |(p x - q x) * r x * m| ≤ |p x * r x * m| + M * |B.indicator q x * m| := by
  by_cases hb : band x
  · rw [Set.indicator_of_mem (hB hb)]
    have e : (p x - q x) * r x * m = p x * r x * m - r x * (q x * m) := by ring
    rw [e]
    refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hr hb) (abs_nonneg _)
  · rw [h0 hb, mul_zero, zero_mul, abs_zero]
    positivity

theorem integral_combo {d : ℕ} {a b r₁ r₂ r₃ : (Fin d → ℂ) → ℝ} (ha : Integrable a) (hb : Integrable b)
    (h₁ : Integrable r₁) (h₂ : Integrable r₂) (h₃ : Integrable r₃) (c₁ c₂ : ℝ)
    (hpt : ∀ y, a y - b y = c₁ * r₁ y + c₂ * (r₂ y - r₃ y)) :
    (∫ y, a y) - ∫ y, b y = c₁ * (∫ y, r₁ y) + c₂ * ((∫ y, r₂ y) - ∫ y, r₃ y) := by
  have i1 : Integrable (fun y => c₁ * r₁ y) := h₁.const_mul c₁
  have i23 : Integrable (fun y => c₂ * (r₂ y - r₃ y)) := (h₂.sub h₃).const_mul c₂
  rw [← integral_sub ha hb, integral_sub h₂ h₃ |>.symm, ← integral_const_mul, ← integral_const_mul,
    ← integral_add i1 i23]
  exact congrArg (fun f : (Fin d → ℂ) → ℝ => ∫ y, f y) (funext hpt)

end SliceCutChain

theorem SliceCutChain.proof (hM : ChartMassCompact.Statement) (hLI : LogIntegrable.Statement) :
    SliceCutChain.Statement := by
  intro n e h J F u ℓ k hJ hF hu hℓ
  obtain ⟨hI, hdim, hsl⟩ := SliceIdeal.proof n (e + 1) J F ℓ hJ hF hℓ
  have huI := hsl u hu
  set I := J ⊔ Ideal.span {linForm ℓ - 1} with hIdef
  unfold varInt
  split_ifs with hA
  swap
  · simp
  unfold chartInt
  set A := hA.choose with hAdef
  have hAf : IsFiniteProjection I A := hA.choose_spec
  have hfin : ∀ y, (fibre I A y).Finite := fun y => (FibreBound.proof n (e + 1) I A hI hdim hAf y).2.1
  have hne : ∀ x ∈ zeroSet I, x ≠ 0 := by
    intro x hx h0
    have := hx _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self (linForm ℓ - 1)))
    subst h0
    simp [linForm] at this

  have hTs : SmoothNear (zeroSet I) (fun x => Real.log (h.dualNorm x)) :=
    ⟨{0}ᶜ, isOpen_compl_singleton, fun x hx => hne x hx, contDiffOn_log_dualNorm h⟩
  have hT2s : SmoothNear (zeroSet I) (fun x => Real.log (h.dualNorm x) ^ 2 / 2) :=
    ⟨{0}ᶜ, isOpen_compl_singleton, fun x hx => hne x hx, ((contDiffOn_log_dualNorm h).pow 2).div_const 2⟩
  have hω : ∀ i : Fin (e + 1), SmoothNear (zeroSet I)
      ((fun _ x => Real.log (h.dualNorm x) : Fin (e + 1) → (Fin n → ℂ) → ℝ) i) := fun _ => hTs
  have hcons : ∀ f : (Fin n → ℂ) → ℝ, SmoothNear (zeroSet I) f → ∀ i, SmoothNear (zeroSet I)
      ((vecCons f fun _ x => Real.log (h.dualNorm x) : Fin (e + 1) → (Fin n → ℂ) → ℝ) i) := by
    intro f hf i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hf
    · simpa using hTs
  have hΦ1 := hcons _ (smoothNear_of_contDiff (SliceCut.contDiff h k))
  have hΦ2 := hcons _ hT2s

  have hTc : ContinuousOn (fun x => Real.log (h.dualNorm x)) (zeroSet I) :=
    (contDiffOn_log_dualNorm h).continuousOn.mono fun x hx => hne x hx
  have hTm : Measurable (fun x : Fin n → ℂ => Real.log (h.dualNorm x)) :=
    Real.measurable_log.comp (SliceCut.continuous_dualNorm h).measurable
  have hLm : Measurable (fun x : Fin n → ℂ => Real.log ‖linEval u x‖) := by
    refine Real.measurable_log.comp (Continuous.measurable ?_)
    unfold linEval
    fun_prop
  have hsm : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  obtain ⟨-, hτ1⟩ := contDiff_infty_iff_deriv.1 hsm
  obtain ⟨-, hτ2⟩ := contDiff_infty_iff_deriv.1 hτ1
  have hτ1c := hτ1.continuous
  have hτ2c := hτ2.continuous
  obtain ⟨Cτ, hCτ0, hCτ⟩ := smoothTransition_deriv_bound
  have hd0 : ∀ r, r ∉ Set.Icc (0 : ℝ) 1 → deriv Real.smoothTransition r = 0 := by
    intro r hr
    obtain ⟨c, hc⟩ := smoothTransition_eventually_const hr
    rw [hc.deriv_eq, deriv_const]
  have hd1 : ∀ r, r ∉ Set.Icc (0 : ℝ) 1 → deriv (deriv Real.smoothTransition) r = 0 := by
    intro r hr
    have hev : deriv Real.smoothTransition =ᶠ[𝓝 r] fun _ => (0 : ℝ) := by
      filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hr] with r' hr'
      exact hd0 r' hr'
    rw [hev.deriv_eq, deriv_const]
  have ham : Measurable (fun x : Fin n → ℂ => 2 - Real.log (h.dualNorm x) / ((k : ℝ) + 1)) :=
    measurable_const.sub (hTm.div_const _)
  have hacont : ContinuousOn (fun x : Fin n → ℂ => 2 - Real.log (h.dualNorm x) / ((k : ℝ) + 1)) (zeroSet I) :=
    continuousOn_const.sub (hTc.div_const _)

  set E := Real.exp (2 * ((k : ℝ) + 1)) with hE
  obtain ⟨R, hR⟩ := (SliceCut.isCompact_sublevel h E).isBounded.subset_closedBall 0
  have hband : ∀ x, 2 - Real.log (h.dualNorm x) / ((k : ℝ) + 1) ∈ Set.Icc (0 : ℝ) 1 →
      h.dualNorm x ≤ E ∧ |Real.log (h.dualNorm x)| ≤ 2 * ((k : ℝ) + 1) := by
    intro x hx
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    obtain ⟨h0, h1⟩ := hx
    have ht1 : (k : ℝ) + 1 ≤ Real.log (h.dualNorm x) := by
      have : 1 ≤ Real.log (h.dualNorm x) / ((k : ℝ) + 1) := by linarith
      rwa [le_div_iff₀ hk, one_mul] at this
    have ht2 : Real.log (h.dualNorm x) ≤ 2 * ((k : ℝ) + 1) := by
      have : Real.log (h.dualNorm x) / ((k : ℝ) + 1) ≤ 2 := by linarith
      rwa [div_le_iff₀ hk] at this
    have hpos : 0 < h.dualNorm x := by
      by_contra hn
      have h00 : h.dualNorm x = 0 := le_antisymm (not_lt.mp hn) (Real.sqrt_nonneg _)
      rw [h00, Real.log_zero] at ht1
      linarith
    exact ⟨(Real.log_le_iff_le_exp hpos).mp ht2, abs_le.mpr ⟨by linarith, ht2⟩⟩
  have hcs : ∀ W : (Fin n → ℂ) → ℝ,
      (∀ x, 2 - Real.log (h.dualNorm x) / ((k : ℝ) + 1) ∉ Set.Icc (0 : ℝ) 1 → W x = 0) → HasCompactSupport W :=
    fun W hW => HasCompactSupport.intro (SliceCut.isCompact_sublevel h E) fun x hx =>
      hW x fun hb => hx (hband x hb).1
  have hfk0 : ∀ x, E < h.dualNorm x → sliceCut h k x = 0 := by
    intro x hx
    unfold sliceCut
    refine Real.smoothTransition.zero_of_nonpos ?_
    have hpos : 0 < h.dualNorm x := (Real.exp_pos _).trans hx
    have hlog : 2 * ((k : ℝ) + 1) < Real.log (h.dualNorm x) := by
      rw [Real.lt_log_iff_exp_lt hpos]; exact hx
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [sub_nonpos, le_div_iff₀ hk]
    linarith

  have hsheet : ∀ y, ∀ x ∈ fibre I A y, ∀ s, IsSheetAt I A x s →
      A *ᵥ x = y ∧ s y = x ∧ x ≠ 0 ∧ ContDiffAt ℝ 2 s y := by
    intro y x hx s hs
    obtain ⟨hxz, hxy⟩ := hx
    have han := CutOffBoundaryBound.analyticAt_of_isSheetAt hs
    obtain ⟨U, -, -, -, hsx, -⟩ := hs
    subst hxy
    exact ⟨rfl, hsx, hne x hxz, han.contDiffAt.restrict_scalars ℝ⟩
  have hvan : ∀ y, ∀ x ∈ fibre I A y, ∀ s, IsSheetAt I A x s → x ∉ Metric.closedBall (0 : Fin n → ℂ) R →
      maDens (fun i => (vecCons (sliceCut h k) fun _ x => Real.log (h.dualNorm x) :
        Fin (e + 1) → (Fin n → ℂ) → ℝ) i ∘ s) y = 0 := by
    intro y x hx s hs hxR
    obtain ⟨-, hsx, -, hsd⟩ := hsheet y x hx s hs
    have hxE : E < h.dualNorm x := by
      by_contra hc
      exact hxR (hR (not_lt.mp hc))
    have hcont : ContinuousAt (fun w => h.dualNorm (s w)) y :=
      (SliceCut.continuous_dualNorm h).continuousAt.comp hsd.continuousAt
    have hO : ∀ᶠ w in 𝓝 y, E < h.dualNorm (s w) :=
      hcont.tendsto.eventually (lt_mem_nhds (show E < h.dualNorm (s y) by rw [hsx]; exact hxE))
    rw [vecCons_comp]
    refine CutOffBoundaryBound.maDens_cons_eq_zero _ _ y ?_
    filter_upwards [hO] with w hw
    exact hfk0 (s w) hw

  refine SliceCutChain.integral_combo ?_ ?_ ?_ ?_ ?_ _ _ ?_
  · exact CutOffBoundaryBound.integrable_chartDens hM hI hdim hAf hTc hΦ1
      (Or.inr ⟨0, by simpa using SliceCut.hasCompactSupport h k⟩)
  · refine SliceCutChain.integrable_of_dom (M := 1)
      (SheetSumMeasurable.proof n (e + 1) I A _ _ hI hdim hAf hLm hΦ1).1
      (hM n (e + 1) I A _ _ hI hdim hAf hTc hΦ1 (Or.inr ⟨0, by simpa using SliceCut.hasCompactSupport h k⟩))
      (hLI n (e + 1) I A u _ R hI hdim hAf huI hΦ1)
      (SliceCutChain.abs_chartDens_le_add hfin _ _ _ _ 1 fun y x hx s hs => ?_)
    by_cases hxR : x ∈ Metric.closedBall (0 : Fin n → ℂ) R
    · rw [Set.indicator_of_mem hxR, one_mul]
      exact le_add_of_nonneg_left (abs_nonneg _)
    · rw [hvan y x hx s hs hxR]
      simp
  · refine SliceCutChain.integrable_of_dom (M := Cτ)
      (SheetSumMeasurable.proof n (e + 1) I A _ _ hI hdim hAf
        ((hTm.sub hLm).mul (hτ1c.measurable.comp ham)) hω).1
      (hM n (e + 1) I A (fun x => Real.log (h.dualNorm x) *
          deriv Real.smoothTransition (2 - Real.log (h.dualNorm x) / ((k : ℝ) + 1))) _ hI hdim hAf
        (hTc.mul (hτ1c.comp_continuousOn hacont)) hω
        (Or.inl (hcs _ fun x hb => by simp [hd0 _ hb])))
      (hLI n (e + 1) I A u _ R hI hdim hAf huI hω)
      (SliceCutChain.abs_chartDens_le_add hfin _ _ _ _ Cτ fun y x hx s hs =>
        SliceCutChain.term_dom (Metric.closedBall 0 R)
          (fun x => 2 - Real.log (h.dualNorm x) / ((k : ℝ) + 1) ∈ Set.Icc (0 : ℝ) 1)
          (fun x => Real.log (h.dualNorm x)) (fun x => Real.log ‖linEval u x‖)
          (fun x => deriv Real.smoothTransition (2 - Real.log (h.dualNorm x) / ((k : ℝ) + 1))) Cτ _ x
          (fun hb => hd0 _ hb) (fun hb => hR (hband x hb).1) (fun _ => (hCτ _).1) hCτ0)
  · refine SliceCutChain.integrable_of_dom (M := Cτ)
      (SheetSumMeasurable.proof n (e + 1) I A _ _ hI hdim hAf
        ((hTm.sub hLm).mul (hτ2c.measurable.comp ham)) hΦ2).1
      (hM n (e + 1) I A (fun x => Real.log (h.dualNorm x) *
          deriv (deriv Real.smoothTransition) (2 - Real.log (h.dualNorm x) / ((k : ℝ) + 1))) _ hI hdim hAf
        (hTc.mul (hτ2c.comp_continuousOn hacont)) hΦ2
        (Or.inl (hcs _ fun x hb => by simp [hd1 _ hb])))
      (hLI n (e + 1) I A u _ R hI hdim hAf huI hΦ2)
      (SliceCutChain.abs_chartDens_le_add hfin _ _ _ _ Cτ fun y x hx s hs =>
        SliceCutChain.term_dom (Metric.closedBall 0 R)
          (fun x => 2 - Real.log (h.dualNorm x) / ((k : ℝ) + 1) ∈ Set.Icc (0 : ℝ) 1)
          (fun x => Real.log (h.dualNorm x)) (fun x => Real.log ‖linEval u x‖)
          (fun x => deriv (deriv Real.smoothTransition) (2 - Real.log (h.dualNorm x) / ((k : ℝ) + 1))) Cτ _ x
          (fun hb => hd1 _ hb) (fun hb => hR (hband x hb).1) (fun _ => (hCτ _).2) hCτ0)
  · refine SliceCutChain.integrable_of_dom (M := Cτ * (2 * ((k : ℝ) + 1)))
      (SheetSumMeasurable.proof n (e + 1) I A _ _ hI hdim hAf
        (((hTm.sub hLm).mul (hτ2c.measurable.comp ham)).mul hTm) hω).1
      (hM n (e + 1) I A (fun x => Real.log (h.dualNorm x) *
          (deriv (deriv Real.smoothTransition) (2 - Real.log (h.dualNorm x) / ((k : ℝ) + 1)) *
            Real.log (h.dualNorm x))) _ hI hdim hAf
        (hTc.mul ((hτ2c.comp_continuousOn hacont).mul hTc)) hω
        (Or.inl (hcs _ fun x hb => by simp [hd1 _ hb])))
      (hLI n (e + 1) I A u _ R hI hdim hAf huI hω)
      (SliceCutChain.abs_chartDens_le_add hfin _ _ _ _ _ fun y x hx s hs => ?_)
    have H := SliceCutChain.term_dom (Metric.closedBall 0 R)
      (fun x => 2 - Real.log (h.dualNorm x) / ((k : ℝ) + 1) ∈ Set.Icc (0 : ℝ) 1)
      (fun x => Real.log (h.dualNorm x)) (fun x => Real.log ‖linEval u x‖)
      (fun x => deriv (deriv Real.smoothTransition) (2 - Real.log (h.dualNorm x) / ((k : ℝ) + 1)) *
        Real.log (h.dualNorm x)) (Cτ * (2 * ((k : ℝ) + 1)))
      (maDens (fun i => (fun _ x => Real.log (h.dualNorm x) : Fin (e + 1) → (Fin n → ℂ) → ℝ) i ∘ s) y) x
      (fun hb => by simp only [hd1 _ hb, zero_mul]) (fun hb => hR (hband x hb).1)
      (fun hb => by
        rw [abs_mul]
        exact mul_le_mul (hCτ _).2 (hband x hb).2 (abs_nonneg _) hCτ0)
      (by positivity)
    convert H using 2
    ring
  · intro y
    unfold chartDens
    refine SliceCutChain.sheetSum_combo (hfin y) _ _ _ _ _ _ _ fun x hx s hs => ?_
    obtain ⟨-, hsx, hx0, hsd⟩ := hsheet y x hx s hs
    have key := SliceCutChain.sheet_identity h k s y (by rw [hsx]; exact hx0) hsd
    rw [hsx] at key
    beta_reduce
    rw [key]
    ring

end

end GroundTheory.Heights₂.Heights
