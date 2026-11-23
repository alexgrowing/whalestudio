import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegRadialWeight
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StStokesOnChart
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartMassCompact
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRadialPrimitive
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StMaDensLogPow
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PMaDensChain
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PChartMassCompact
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjectionCluster
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffBoundaryBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff

noncomputable section

namespace RegRadialWeight

variable {n : ℕ}

theorem hessC_const {D : ℕ} (c : ℝ) (z : Fin D → ℂ) : hessC (fun _ => c) z = 0 := by
  ext i j
  simp [hessC]

theorem maDens_congr {D : ℕ} {φ φ' : Fin D → (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : ∀ k, hessC (φ k) z = hessC (φ' k) z) : maDens φ z = maDens φ' z := by
  unfold maDens
  simp only [h]

theorem gradDens_congr {m : ℕ} {φ φ' : Fin m → (Fin (m + 1) → ℂ) → ℝ} (v w : (Fin (m + 1) → ℂ) → ℝ)
    {z : Fin (m + 1) → ℂ} (h : ∀ k, hessC (φ k) z = hessC (φ' k) z) :
    gradDens φ v w z = gradDens φ' v w z := by
  unfold gradDens
  simp only [h]

theorem maDens_swap {e : ℕ} (X G : (Fin (e + 1 + 1) → ℂ) → ℝ) (z : Fin (e + 1 + 1) → ℂ) :
    maDens (Fin.cons X (Fin.cons G fun _ : Fin e => X)) z = maDens (Fin.cons G fun _ : Fin (e + 1) => X) z := by
  have h : (fun k => hessC ((Fin.cons X (Fin.cons G fun _ : Fin e => X) : Fin (e + 1 + 1) → _) k) z) =
      (fun k => hessC ((Fin.cons G fun _ : Fin (e + 1) => X : Fin (e + 1 + 1) → _) k) z) ∘
        Equiv.swap 0 1 := by
    funext k
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) i) k
    · simp [Equiv.swap_apply_left]
    · simp [Equiv.swap_apply_right]
    · have h0 : (j.succ.succ : Fin (e + 1 + 1)) ≠ 0 := Fin.succ_ne_zero _
      have h1 : (j.succ.succ : Fin (e + 1 + 1)) ≠ 1 := by
        intro h; exact Fin.succ_ne_zero j (Fin.succ_injective _ h)
      simp [Equiv.swap_apply_of_ne_of_ne h0 h1]
  unfold maDens
  rw [h, mdisc_comp_perm]

theorem euclPot_nonneg' (z : Fin n → ℂ) : 0 ≤ euclPot z :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem hessC_euclPot_comp {D : ℕ} {s : (Fin D → ℂ) → Fin n → ℂ} {y : Fin D → ℂ} (hs : AnalyticAt ℂ s y)
    (x : Fin n → ℂ) : hessC (euclPot ∘ s) y = hessC (fun w => euclPot (s w - x)) y := by
  have hsC : ContDiffAt ℝ 2 s y := hs.contDiffAt.restrict_scalars ℝ
  have hE : ContDiffAt ℝ 2 (euclPot ∘ s) y :=
    ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt.comp y hsC
  have hsj : ∀ j, AnalyticAt ℂ (fun w => s w j) y := analyticAt_pi_iff.1 hs
  have hG : AnalyticAt ℂ (fun w => ∑ j, (-2 * (s w j * (starRingEnd ℂ) (x j)) + (Complex.normSq (x j) : ℂ))) y :=
    Finset.analyticAt_fun_sum _ fun j _ =>
      (analyticAt_const.mul ((hsj j).mul analyticAt_const)).add analyticAt_const
  have heq : (fun w => euclPot (s w - x)) = fun w => (euclPot ∘ s) w +
      (∑ j, (-2 * (s w j * (starRingEnd ℂ) (x j)) + (Complex.normSq (x j) : ℂ))).re := by
    funext w
    simp only [euclPot, Function.comp_apply, Pi.sub_apply, Complex.re_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
    simp [Complex.mul_re]
    ring
  rw [heq, hessC_add_re_analytic _ _ y hE hG]

theorem hasCompactSupport_radial (x : Fin n → ℂ) (F : ℝ → ℝ) (R : ℝ) (hF : ∀ t, R ≤ t → F t = 0) :
    HasCompactSupport (fun z : Fin n → ℂ => F (euclPot (z - x))) := by
  refine HasCompactSupport.intro (isCompact_closedBall x (Real.sqrt |R|)) fun z hz => ?_
  by_contra hne
  apply hz
  have hlt : euclPot (z - x) < R := by
    by_contra h
    exact hne (hF _ (not_lt.mp h))
  rw [Metric.mem_closedBall, dist_eq_norm]
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => ?_
  have hj : ‖(z - x) j‖ ^ 2 ≤ euclPot (z - x) :=
    Finset.single_le_sum (f := fun j => ‖(z - x) j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ j)
  calc ‖(z - x) j‖ = Real.sqrt (‖(z - x) j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt |R| := Real.sqrt_le_sqrt (by linarith [le_abs_self R])

theorem sheet_identity (hLP : MaDensLogPow.Statement) {e : ℕ} {s : (Fin (e + 1 + 1) → ℂ) → Fin n → ℂ}
    {y : Fin (e + 1 + 1) → ℂ} (hs : AnalyticAt ℂ s y) (x : Fin n → ℂ) (G : (Fin n → ℂ) → ℝ) (Q a b : ℝ → ℝ)
    (hQ : ContDiff ℝ 2 Q) (hQ0 : deriv Q 0 = a 0) (hQ0' : deriv (deriv Q) 0 = 0) (hb0 : b 0 = 0)
    (hQt : ∀ t, 0 < t → deriv Q t * t ^ (e + 1) = a t * t ^ (e + 1) - b t ∧
      deriv (deriv Q) t * t ^ (e + 2) = ((e + 1 : ℕ) : ℝ) * b t) :
    b (euclPot (s y - x)) * maDens (fun k => vecCons G (fun _ : Fin (e + 1) => logDistSq x) k ∘ s) y =
      a (euclPot (s y - x)) * maDens (fun k => vecCons G (fun _ : Fin (e + 1) => euclPot) k ∘ s) y -
        1 * maDens (fun k => vecCons (fun z => Q (euclPot (z - x))) (vecCons G fun _ : Fin e => euclPot) k ∘ s) y := by
  have hsC : ContDiffAt ℝ 2 s y := hs.contDiffAt.restrict_scalars ℝ
  have hp2 : ContDiffAt ℝ 2 (fun w => euclPot (s w - x)) y :=
    ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt.comp y (hsC.sub contDiffAt_const)
  have hE := hessC_euclPot_comp hs x
  have h1 : (fun k => vecCons G (fun _ : Fin (e + 1) => logDistSq x) k ∘ s) =
      Fin.cons (G ∘ s) (fun _ : Fin (e + 1) => Real.log ∘ fun w => euclPot (s w - x)) := by
    funext k
    refine Fin.cases rfl (fun i => rfl) k
  have h2 : maDens (fun k => vecCons G (fun _ : Fin (e + 1) => euclPot) k ∘ s) y =
      maDens (Fin.cons (G ∘ s) fun _ : Fin (e + 1) => fun w => euclPot (s w - x)) y := by
    apply maDens_congr
    intro k
    refine Fin.cases rfl (fun i => ?_) k
    exact hE
  have h3 : maDens (fun k => vecCons (fun z => Q (euclPot (z - x))) (vecCons G fun _ : Fin e => euclPot) k ∘ s) y =
      deriv Q (euclPot (s y - x)) * maDens (Fin.cons (G ∘ s) fun _ : Fin (e + 1) => fun w => euclPot (s w - x)) y +
        deriv (deriv Q) (euclPot (s y - x)) *
          gradDens (Fin.cons (G ∘ s) fun _ : Fin e => fun w => euclPot (s w - x))
            (fun w => euclPot (s w - x)) (fun w => euclPot (s w - x)) y := by
    have hc := (MaDensChain.proof (e + 1) (Fin.cons (G ∘ s) fun _ : Fin e => euclPot ∘ s) Q
      (fun w => euclPot (s w - x)) y hQ hp2).1
    have hfun : (fun k => vecCons (fun z => Q (euclPot (z - x))) (vecCons G fun _ : Fin e => euclPot) k ∘ s) =
        Fin.cons (Q ∘ fun w => euclPot (s w - x)) (Fin.cons (G ∘ s) fun _ : Fin e => euclPot ∘ s) := by
      funext k
      refine Fin.cases rfl (fun i => Fin.cases rfl (fun j => rfl) i) k
    have hm : maDens (Fin.cons (fun w => euclPot (s w - x)) (Fin.cons (G ∘ s) fun _ : Fin e => euclPot ∘ s)) y =
        maDens (Fin.cons (G ∘ s) fun _ : Fin (e + 1) => fun w => euclPot (s w - x)) y := by
      rw [maDens_congr (φ' := Fin.cons (fun w => euclPot (s w - x))
        (Fin.cons (G ∘ s) fun _ : Fin e => fun w => euclPot (s w - x))), maDens_swap]
      intro k
      refine Fin.cases rfl (fun i => Fin.cases rfl (fun j => ?_) i) k
      exact hE
    have hg : gradDens (Fin.cons (G ∘ s) fun _ : Fin e => euclPot ∘ s) (fun w => euclPot (s w - x))
        (fun w => euclPot (s w - x)) y =
        gradDens (Fin.cons (G ∘ s) fun _ : Fin e => fun w => euclPot (s w - x))
          (fun w => euclPot (s w - x)) (fun w => euclPot (s w - x)) y := by
      apply gradDens_congr
      intro k
      refine Fin.cases rfl (fun j => ?_) k
      exact hE
    rw [hfun, hc, hm, hg]
  rw [h1, h2, h3]
  have hp0 : 0 ≤ euclPot (s y - x) := euclPot_nonneg' _
  rcases hp0.eq_or_lt with h | h
  · rw [← h, hb0, hQ0, hQ0']
    ring
  · rw [hLP e (G ∘ s) (fun w => euclPot (s w - x)) y hp2 h]
    obtain ⟨e1, e2⟩ := hQt _ h
    have ht1 : euclPot (s y - x) ^ (e + 1) ≠ 0 := pow_ne_zero _ h.ne'
    have ht2 : euclPot (s y - x) ^ (e + 2) ≠ 0 := pow_ne_zero _ h.ne'
    have hQ' : deriv Q (euclPot (s y - x)) =
        (a (euclPot (s y - x)) * euclPot (s y - x) ^ (e + 1) - b (euclPot (s y - x))) /
          euclPot (s y - x) ^ (e + 1) := by
      rw [eq_div_iff ht1]
      exact e1
    have hQ'' : deriv (deriv Q) (euclPot (s y - x)) =
        ((e + 1 : ℕ) : ℝ) * b (euclPot (s y - x)) / euclPot (s y - x) ^ (e + 2) := by
      rw [eq_div_iff ht2]
      exact e2
    rw [hQ', hQ'']
    field_simp
    ring

theorem norm_chartDens_le {D : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin D) (Fin n) ℂ)
    (hA : IsFiniteProjection J A) (f : (Fin n → ℂ) → ℝ) (φ : Fin D → (Fin n → ℂ) → ℝ) (y : Fin D → ℂ) :
    ‖chartDens J A f φ y‖ ≤ chartAbsDens J A f φ y := by
  classical
  have hfin : (fibre J A y).Finite := FiniteProjectionCluster.fibre_finite J A hA y
  unfold chartDens chartAbsDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin, Real.norm_eq_abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x' _ => ?_)
  split_ifs <;> simp

theorem maDens_const_position {m : ℕ} (c : ℝ) (φ : Fin m → (Fin n → ℂ) → ℝ)
    (s : (Fin (m + 1) → ℂ) → Fin n → ℂ) (y : Fin (m + 1) → ℂ) :
    maDens (fun k => (vecCons (fun _ => c) φ : Fin (m + 1) → (Fin n → ℂ) → ℝ) k ∘ s) y = 0 := by
  unfold maDens
  rw [ChartMassCompact.mdisc_coord_zero _ 0 (hessC_const c y)]
  simp

theorem chartDens_eq (hLP : MaDensLogPow.Statement) {e : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (A : Matrix (Fin (e + 1 + 1)) (Fin n) ℂ) (hA : IsFiniteProjection J A) (x : Fin n → ℂ)
    (G : (Fin n → ℂ) → ℝ) (Q a b : ℝ → ℝ)
    (hQ : ContDiff ℝ 2 Q) (hQ0 : deriv Q 0 = a 0) (hQ0' : deriv (deriv Q) 0 = 0) (hb0 : b 0 = 0)
    (hQt : ∀ t, 0 < t → deriv Q t * t ^ (e + 1) = a t * t ^ (e + 1) - b t ∧
      deriv (deriv Q) t * t ^ (e + 2) = ((e + 1 : ℕ) : ℝ) * b t) (y : Fin (e + 1 + 1) → ℂ) :
    chartDens J A (fun z => b (euclPot (z - x))) (vecCons G fun _ : Fin (e + 1) => logDistSq x) y =
      chartDens J A (fun z => a (euclPot (z - x))) (vecCons G fun _ : Fin (e + 1) => euclPot) y -
        chartDens J A (fun _ => 1) (vecCons (fun z => Q (euclPot (z - x))) (vecCons G fun _ : Fin e => euclPot)) y := by
  classical
  have hfin : (fibre J A y).Finite := FiniteProjectionCluster.fibre_finite J A hA y
  unfold chartDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x' hx' => ?_
  rw [Set.Finite.mem_toFinset] at hx'
  obtain ⟨-, rfl⟩ := hx'
  split_ifs with h
  · have hsx : h.choose (A *ᵥ x') = x' := by
      obtain ⟨U, -, -, -, hsx, -⟩ := h.choose_spec
      exact hsx
    have key := sheet_identity hLP (CutOffBoundaryBound.analyticAt_of_isSheetAt h.choose_spec) x G Q a b hQ
      hQ0 hQ0' hb0 hQt
    rw [hsx] at key
    exact key
  · simp

theorem smoothNear_cons {m : ℕ} {S : Set (Fin n → ℂ)} {g : (Fin n → ℂ) → ℝ} {φ : Fin m → (Fin n → ℂ) → ℝ}
    (hg : SmoothNear S g) (hφ : ∀ i, SmoothNear S (φ i)) : ∀ i, SmoothNear S (vecCons g φ i) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hg
  · exact hφ j

end RegRadialWeight

open RegRadialWeight in

theorem RegRadialWeight.proof (hS : StokesOnChart.Statement) (hM : ChartMassCompact.Statement)
    (hRP : RadialPrimitive.Statement) (hLP : MaDensLogPow.Statement) : RegRadialWeight.Statement := by
  intro n d J A u ε x a t₀ T hJ hd hA hε ha ht₀ hconst hT hint
  cases d with
  | zero =>
    have h : (fun _ : Fin 0 => (euclPot : (Fin n → ℂ) → ℝ)) = fun _ : Fin 0 => logDistSq x :=
      funext fun i => i.elim0
    rw [h, radialTransform_zero]
  | succ e =>
    obtain ⟨Q, hQ, ⟨R, hR⟩, hQ0, hQ0', hQt⟩ := hRP e a t₀ T ha ht₀ hconst hT hint
    have hQ2 : ContDiff ℝ 2 Q := hQ.of_le (WithTop.coe_le_coe.mpr le_top)
    have hψ : ContDiff ℝ ∞ (fun z : Fin n → ℂ => euclPot (z - x)) :=
      (contDiff_euclPot n).comp (contDiff_id.sub contDiff_const)
    have hQψ : ContDiff ℝ ∞ (fun z : Fin n → ℂ => Q (euclPot (z - x))) := hQ.comp hψ
    have hcsQ := hasCompactSupport_radial x Q R hR
    have hcsa := hasCompactSupport_radial x a T hT
    have hb0 : radialTransform (e + 1) a 0 = 0 :=
      radialTransform_eq_zero_of_const e a hconst ⟨le_refl 0, ht₀.le⟩
    have hsE : ∀ i : Fin e, SmoothNear (zeroSet J) ((fun _ => euclPot) i) :=
      fun _ => smoothNear_of_contDiff (contDiff_euclPot n)
    have hsE' : ∀ i : Fin (e + 1), SmoothNear (zeroSet J) ((fun _ => euclPot) i) :=
      fun _ => smoothNear_of_contDiff (contDiff_euclPot n)
    have hsg : SmoothNear (zeroSet J) (logReg u ε) := smoothNear_of_contDiff (contDiff_logReg u hε)
    have hsφ := smoothNear_cons hsg hsE
    have hsφ₁ := smoothNear_cons (smoothNear_of_contDiff hQψ) hsφ
    have hsφ₂ := smoothNear_cons hsg hsE'

    have hSt := hS n (e + 1) J A (fun z => Q (euclPot (z - x))) (fun _ => 1)
      (vecCons (logReg u ε) fun _ : Fin e => euclPot) hJ hd hA (smoothNear_of_contDiff hQψ)
      (smoothNear_of_contDiff contDiff_const) hsφ (Or.inl hcsQ)
    have hzero : ∫ y, chartDens J A (fun _ => 1)
        (vecCons (fun z => Q (euclPot (z - x))) (vecCons (logReg u ε) fun _ : Fin e => euclPot)) y = 0 := by
      have h0 : ∀ y, chartDens J A (fun z => Q (euclPot (z - x)))
          (vecCons (fun _ => (1 : ℝ)) (vecCons (logReg u ε) fun _ : Fin e => euclPot)) y = 0 := by
        intro y
        have hterm : ∀ x' (s : (Fin (e + 1 + 1) → ℂ) → Fin n → ℂ),
            Q (euclPot (x' - x)) * maDens (fun k => (vecCons (fun _ => (1 : ℝ))
              (vecCons (logReg u ε) fun _ : Fin e => euclPot)) k ∘ s) y = 0 := by
          intro x' s
          rw [maDens_const_position 1 _ s y, mul_zero]
        unfold chartDens sheetSum
        simp [hterm]
      unfold chartInt at hSt
      rw [← hSt]
      simp [h0]

    have hint1 : Integrable (chartDens J A (fun _ => 1)
        (vecCons (fun z => Q (euclPot (z - x))) (vecCons (logReg u ε) fun _ : Fin e => euclPot))) :=
      (hM n (e + 1 + 1) J A _ _ hJ hd hA continuousOn_const hsφ₁ (Or.inr ⟨0, hcsQ⟩)).mono'
        ((SheetSumMeasurable.proof n (e + 1 + 1) J A _ _ hJ hd hA measurable_const hsφ₁).1.aestronglyMeasurable)
        (Eventually.of_forall fun y => norm_chartDens_le J A hA _ _ y)
    have hint2 : Integrable (chartDens J A (fun z => a (euclPot (z - x)))
        (vecCons (logReg u ε) fun _ : Fin (e + 1) => euclPot)) :=
      (hM n (e + 1 + 1) J A _ _ hJ hd hA (ha.continuous.comp hψ.continuous).continuousOn hsφ₂
        (Or.inl hcsa)).mono'
        ((SheetSumMeasurable.proof n (e + 1 + 1) J A _ _ hJ hd hA
          (ha.continuous.comp hψ.continuous).measurable hsφ₂).1.aestronglyMeasurable)
        (Eventually.of_forall fun y => norm_chartDens_le J A hA _ _ y)
    have hpt := chartDens_eq hLP J A hA x (logReg u ε) Q a (radialTransform (e + 1) a) hQ2 hQ0 hQ0' hb0 hQt
    calc ∫ y, chartDens J A (fun z => a (euclPot (z - x))) (vecCons (logReg u ε) fun _ => euclPot) y
        = (∫ y, chartDens J A (fun z => a (euclPot (z - x))) (vecCons (logReg u ε) fun _ => euclPot) y) -
            ∫ y, chartDens J A (fun _ => 1)
              (vecCons (fun z => Q (euclPot (z - x))) (vecCons (logReg u ε) fun _ : Fin e => euclPot)) y := by
          rw [hzero, sub_zero]
      _ = ∫ y, (chartDens J A (fun z => a (euclPot (z - x))) (vecCons (logReg u ε) fun _ => euclPot) y -
            chartDens J A (fun _ => 1)
              (vecCons (fun z => Q (euclPot (z - x))) (vecCons (logReg u ε) fun _ : Fin e => euclPot)) y) :=
          (integral_sub hint2 hint1).symm
      _ = _ := by
          congr 1
          funext y
          exact (hpt y).symm

end

end GroundTheory.Heights₂.Heights
