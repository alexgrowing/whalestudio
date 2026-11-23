import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersSemilocalMaxIdeals
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegMassNearSmall
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegBallMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegFormCompare
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegLelongMono
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegLelongAnnulus
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegRadialWeight
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRadialPrimitive
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PMaDensLogPow
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegLogDensNonneg
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSmallSetBallCover
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSmallSetTubeVolume
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimeTubeVolume
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVarietyMassLower
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTangentGraphLowerDensity
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVarietyTangentGraphDense
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVarietyLelongMono
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVarWirtinger
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVarLelongMono
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLinearNoetherNormalization
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.VarLelong

open GroundTheory.Heights₂.Heights MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff

noncomputable section

variable {n : ℕ}

theorem cons_const_apply' {e : ℕ} (G H : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (k : Fin (e + 1)) :
    (Fin.cons G (fun _ : Fin e => H) : Fin (e + 1) → _) k = if k = 0 then G else H := by
  refine Fin.cases ?_ (fun i => ?_) k
  · simp
  · simp [Fin.succ_ne_zero]

theorem mdisc_update_const {e : ℕ} (G H : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (i : Fin (e + 1)) :
    mdisc (Function.update (fun _ : Fin (e + 1) => H) i G) =
      mdisc (Fin.cons G (fun _ : Fin e => H) : Fin (e + 1) → _) := by
  rw [← mdisc_comp_perm (Fin.cons G (fun _ : Fin e => H) : Fin (e + 1) → _) (Equiv.swap 0 i)]
  congr 1
  funext k
  simp only [Function.comp_apply, cons_const_apply', Function.update_apply]
  by_cases hki : k = i
  · subst hki
    simp
  · have : Equiv.swap 0 i k ≠ 0 := by
      intro h
      apply hki
      have := congrArg (Equiv.swap 0 i) h
      simpa using this
    simp [hki, this]

theorem maDens_log_all {e : ℕ} (p : (Fin (e + 1) → ℂ) → ℝ) (y : Fin (e + 1) → ℂ)
    (hp : ContDiffAt ℝ 2 p y) (hpos : 0 < p y) :
    maDens (fun _ : Fin (e + 1) => Real.log ∘ p) y =
      maDens (fun _ : Fin (e + 1) => p) y / p y ^ (e + 1) -
        ((e + 1 : ℕ) : ℝ) * gradDens (fun _ : Fin e => p) p p y / p y ^ (e + 2) := by
  set H := hessC p y with hH
  set G := gradMat p p y with hGdef
  set a : ℝ := (p y)⁻¹ with ha
  set b : ℝ := -((p y) ^ 2)⁻¹ with hb
  have hlog : hessC (Real.log ∘ p) y = (a : ℂ) • H + (b : ℂ) • G := MaDensLogPow.hessC_log_comp hp hpos
  have hG : ∀ (A : Fin (e + 1) → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (i j : Fin (e + 1)),
      i ≠ j → A i = G → A j = G → mdisc A = 0 := fun A i j hij hi hj =>
    MaDensLogPow.mdisc_eq_zero_of_two_rankOne A _ hij _ _ (hi.trans (gradMat_eq_vecMulVec p p y))
      (hj.trans (gradMat_eq_vecMulVec p p y))
  have key := MaDensLogPow.mdisc_expand (a : ℂ) (b : ℂ) H G hG Finset.univ (fun _ => H) (fun _ _ => rfl)
  rw [Finset.sum_congr rfl fun i _ => mdisc_update_const G H i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Nat.add_sub_cancel, nsmul_eq_mul] at key
  simp only [Finset.mem_univ, if_true] at key
  have hfam3 : (fun i => hessC ((fun _ : Fin e => p) i) y) = fun _ : Fin e => H := rfl
  unfold maDens gradDens
  simp only [hlog]
  rw [key]
  have hp0 : p y ≠ 0 := hpos.ne'
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.add_re,
    Complex.re_ofReal_mul]
  rw [← hH, ← hGdef, ha, hb]
  simp only [inv_pow, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

theorem sheet_identity_all {e : ℕ} {s : (Fin (e + 1) → ℂ) → Fin n → ℂ}
    {y : Fin (e + 1) → ℂ} (hs : AnalyticAt ℂ s y) (x : Fin n → ℂ) (Q a b : ℝ → ℝ)
    (hQ : ContDiff ℝ 2 Q) (hQ0 : deriv Q 0 = a 0) (hQ0' : deriv (deriv Q) 0 = 0) (hb0 : b 0 = 0)
    (hQt : ∀ t, 0 < t → deriv Q t * t ^ (e + 1) = a t * t ^ (e + 1) - b t ∧
      deriv (deriv Q) t * t ^ (e + 2) = ((e + 1 : ℕ) : ℝ) * b t) :
    b (euclPot (s y - x)) * maDens (fun k => (fun _ : Fin (e + 1) => logDistSq x) k ∘ s) y =
      a (euclPot (s y - x)) * maDens (fun k => (fun _ : Fin (e + 1) => (euclPot : (Fin n → ℂ) → ℝ)) k ∘ s) y -
        1 * maDens (fun k => (vecCons (fun z => Q (euclPot (z - x)))
          (fun _ : Fin e => (euclPot : (Fin n → ℂ) → ℝ)) : Fin (e + 1) → (Fin n → ℂ) → ℝ) k ∘ s) y := by
  have hsC : ContDiffAt ℝ 2 s y := hs.contDiffAt.restrict_scalars ℝ
  have hp2 : ContDiffAt ℝ 2 (fun w => euclPot (s w - x)) y :=
    ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt.comp y (hsC.sub contDiffAt_const)
  have hE := RegRadialWeight.hessC_euclPot_comp hs x
  have h1 : (fun k => (fun _ : Fin (e + 1) => logDistSq x) k ∘ s) =
      fun _ : Fin (e + 1) => Real.log ∘ fun w => euclPot (s w - x) := rfl
  have h2 : maDens (fun k => (fun _ : Fin (e + 1) => (euclPot : (Fin n → ℂ) → ℝ)) k ∘ s) y =
      maDens (fun _ : Fin (e + 1) => fun w => euclPot (s w - x)) y :=
    RegRadialWeight.maDens_congr fun _ => hE
  have h3 : maDens (fun k => (vecCons (fun z => Q (euclPot (z - x)))
        (fun _ : Fin e => (euclPot : (Fin n → ℂ) → ℝ)) : Fin (e + 1) → (Fin n → ℂ) → ℝ) k ∘ s) y =
      deriv Q (euclPot (s y - x)) * maDens (fun _ : Fin (e + 1) => fun w => euclPot (s w - x)) y +
        deriv (deriv Q) (euclPot (s y - x)) *
          gradDens (fun _ : Fin e => fun w => euclPot (s w - x))
            (fun w => euclPot (s w - x)) (fun w => euclPot (s w - x)) y := by
    have hc := (MaDensChain.proof e (fun _ : Fin e => euclPot ∘ s) Q
      (fun w => euclPot (s w - x)) y hQ hp2).1
    have hfun : (fun k => (vecCons (fun z => Q (euclPot (z - x)))
        (fun _ : Fin e => (euclPot : (Fin n → ℂ) → ℝ)) : Fin (e + 1) → (Fin n → ℂ) → ℝ) k ∘ s) =
        Fin.cons (Q ∘ fun w => euclPot (s w - x)) (fun _ : Fin e => euclPot ∘ s) := by
      funext k
      refine Fin.cases rfl (fun i => rfl) k
    have hm : maDens (Fin.cons (fun w => euclPot (s w - x)) (fun _ : Fin e => euclPot ∘ s)) y =
        maDens (fun _ : Fin (e + 1) => fun w => euclPot (s w - x)) y := by
      apply RegRadialWeight.maDens_congr
      intro k
      refine Fin.cases rfl (fun i => ?_) k
      exact hE
    have hg : gradDens (fun _ : Fin e => euclPot ∘ s) (fun w => euclPot (s w - x))
        (fun w => euclPot (s w - x)) y =
        gradDens (fun _ : Fin e => fun w => euclPot (s w - x))
          (fun w => euclPot (s w - x)) (fun w => euclPot (s w - x)) y :=
      RegRadialWeight.gradDens_congr _ _ fun _ => hE
    rw [hfun, hc, hm, hg]
  rw [h1, h2, h3]
  have hp0 : 0 ≤ euclPot (s y - x) := RegRadialWeight.euclPot_nonneg' _
  rcases hp0.eq_or_lt with h | h
  · rw [← h, hb0, hQ0, hQ0']
    ring
  · rw [maDens_log_all (fun w => euclPot (s w - x)) y hp2 h]
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

theorem chartDens_eq_all {e : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (A : Matrix (Fin (e + 1)) (Fin n) ℂ) (hA : IsFiniteProjection J A) (x : Fin n → ℂ)
    (Q a b : ℝ → ℝ)
    (hQ : ContDiff ℝ 2 Q) (hQ0 : deriv Q 0 = a 0) (hQ0' : deriv (deriv Q) 0 = 0) (hb0 : b 0 = 0)
    (hQt : ∀ t, 0 < t → deriv Q t * t ^ (e + 1) = a t * t ^ (e + 1) - b t ∧
      deriv (deriv Q) t * t ^ (e + 2) = ((e + 1 : ℕ) : ℝ) * b t) (y : Fin (e + 1) → ℂ) :
    chartDens J A (fun z => b (euclPot (z - x))) (fun _ : Fin (e + 1) => logDistSq x) y =
      chartDens J A (fun z => a (euclPot (z - x))) (fun _ : Fin (e + 1) => euclPot) y -
        chartDens J A (fun _ => 1) (vecCons (fun z => Q (euclPot (z - x))) (fun _ : Fin e => euclPot)) y := by
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
    have key := sheet_identity_all (CutOffBoundaryBound.analyticAt_of_isSheetAt h.choose_spec) x Q a b hQ
      hQ0 hQ0' hb0 hQt
    rw [hsx] at key
    exact key
  · simp

theorem varRadialWeight {d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin (d + 1)) (Fin n) ℂ}
    (x : Fin n → ℂ) (a : ℝ → ℝ) (t₀ T : ℝ)
    (hJ : J.IsPrime) (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ))
    (hA : IsFiniteProjection J A) (ha : ContDiff ℝ ∞ a) (ht₀ : 0 < t₀)
    (hconst : ∀ t ∈ Set.Icc 0 t₀, a t = a 0) (hT : ∀ t, T ≤ t → a t = 0)
    (hint : (∫ τ in (0 : ℝ)..T, a τ * (((d + 1 : ℕ) : ℝ) * τ ^ (d + 1 - 1))) = 0) :
    ∫ y, chartDens J A (fun z => a (euclPot (z - x))) (fun _ => euclPot) y =
      ∫ y, chartDens J A (fun z => radialTransform (d + 1) a (euclPot (z - x))) (fun _ => logDistSq x) y := by
  have hS := GroundTheory.Heights₂.Heights.AutoClose.StokesOnChart
  have hM := HilbertSamuel.Closed.ChartMassCompact
  obtain ⟨Q, hQ, ⟨R, hR⟩, hQ0, hQ0', hQt⟩ := RadialPrimitive.proof d a t₀ T ha ht₀ hconst hT hint
  have hQ2 : ContDiff ℝ 2 Q := hQ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hψ : ContDiff ℝ ∞ (fun z : Fin n → ℂ => euclPot (z - x)) :=
    (contDiff_euclPot n).comp (contDiff_id.sub contDiff_const)
  have hQψ : ContDiff ℝ ∞ (fun z : Fin n → ℂ => Q (euclPot (z - x))) := hQ.comp hψ
  have hcsQ := RegRadialWeight.hasCompactSupport_radial x Q R hR
  have hcsa := RegRadialWeight.hasCompactSupport_radial x a T hT
  have hb0 : radialTransform (d + 1) a 0 = 0 :=
    radialTransform_eq_zero_of_const d a hconst ⟨le_refl 0, ht₀.le⟩
  have hsE : ∀ i : Fin d, SmoothNear (zeroSet J) ((fun _ => euclPot) i) :=
    fun _ => smoothNear_of_contDiff (contDiff_euclPot n)
  have hsE' : ∀ i : Fin (d + 1), SmoothNear (zeroSet J) ((fun _ => euclPot) i) :=
    fun _ => smoothNear_of_contDiff (contDiff_euclPot n)
  have hsφ₁ := RegRadialWeight.smoothNear_cons (smoothNear_of_contDiff (S := zeroSet J) hQψ) hsE
  have hSt := hS n d J A (fun z => Q (euclPot (z - x))) (fun _ => 1)
    (fun _ : Fin d => euclPot) hJ hd hA (smoothNear_of_contDiff hQψ)
    (smoothNear_of_contDiff contDiff_const) hsE (Or.inl hcsQ)
  have hzero : ∫ y, chartDens J A (fun _ => 1)
      (vecCons (fun z => Q (euclPot (z - x))) (fun _ : Fin d => euclPot)) y = 0 := by
    have h0 : ∀ y, chartDens J A (fun z => Q (euclPot (z - x)))
        (vecCons (fun _ => (1 : ℝ)) (fun _ : Fin d => euclPot)) y = 0 := by
      intro y
      have hterm : ∀ x' (s : (Fin (d + 1) → ℂ) → Fin n → ℂ),
          Q (euclPot (x' - x)) * maDens (fun k => (vecCons (fun _ => (1 : ℝ))
            (fun _ : Fin d => euclPot)) k ∘ s) y = 0 := by
        intro x' s
        rw [RegRadialWeight.maDens_const_position 1 _ s y, mul_zero]
      unfold chartDens sheetSum
      simp [hterm]
    unfold chartInt at hSt
    rw [← hSt]
    simp [h0]
  have hint1 : Integrable (chartDens J A (fun _ => 1)
      (vecCons (fun z => Q (euclPot (z - x))) (fun _ : Fin d => euclPot))) :=
    (hM n (d + 1) J A _ _ hJ hd hA continuousOn_const hsφ₁ (Or.inr ⟨0, hcsQ⟩)).mono'
      ((SheetSumMeasurable.proof n (d + 1) J A _ _ hJ hd hA measurable_const hsφ₁).1.aestronglyMeasurable)
      (Eventually.of_forall fun y => RegRadialWeight.norm_chartDens_le J A hA _ _ y)
  have hint2 : Integrable (chartDens J A (fun z => a (euclPot (z - x)))
      (fun _ : Fin (d + 1) => euclPot)) :=
    (hM n (d + 1) J A _ _ hJ hd hA (ha.continuous.comp hψ.continuous).continuousOn hsE'
      (Or.inl hcsa)).mono'
      ((SheetSumMeasurable.proof n (d + 1) J A _ _ hJ hd hA
        (ha.continuous.comp hψ.continuous).measurable hsE').1.aestronglyMeasurable)
      (Eventually.of_forall fun y => RegRadialWeight.norm_chartDens_le J A hA _ _ y)
  have hpt := chartDens_eq_all J A hA x Q a (radialTransform (d + 1) a) hQ2 hQ0 hQ0' hb0 hQt
  calc ∫ y, chartDens J A (fun z => a (euclPot (z - x))) (fun _ => euclPot) y
      = (∫ y, chartDens J A (fun z => a (euclPot (z - x))) (fun _ => euclPot) y) -
          ∫ y, chartDens J A (fun _ => 1)
            (vecCons (fun z => Q (euclPot (z - x))) (fun _ : Fin d => euclPot)) y := by
        rw [hzero, sub_zero]
    _ = ∫ y, (chartDens J A (fun z => a (euclPot (z - x))) (fun _ => euclPot) y -
          chartDens J A (fun _ => 1)
            (vecCons (fun z => Q (euclPot (z - x))) (fun _ : Fin d => euclPot)) y) :=
        (integral_sub hint2 hint1).symm
    _ = _ := by
        congr 1
        funext y
        exact (hpt y).symm

open RegLelongAnnulus in

theorem varLelongAnnulus : VarLelongAnnulus.Statement := by
  have hCM := HilbertSamuel.Closed.ChartMassCompact
  intro n d J A x r s hJ hdim hAf hr hrs
  have hs : 0 < s := hr.trans_le hrs
  have hr2 : 0 < r ^ 2 := pow_pos hr 2
  have hs2 : r ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hr.le hrs 2
  have hφσ : ∀ k, SmoothNear (zeroSet J)
      ((fun _ => euclPot : Fin (d + 1) → (Fin n → ℂ) → ℝ) k) :=
    fun _ => smoothNear_of_contDiff (S := zeroSet J) (contDiff_euclPot n)
  have hball : ∀ ρ, 0 < ρ → ρ ≤ s → Integrable (chartDens J A ((euclBall x ρ).indicator fun _ => (1 : ℝ))
      (fun _ : Fin (d + 1) => euclPot)) := by
    intro ρ hρ hρs
    refine integrable_chartDens hCM hJ hdim hAf hφσ (continuous_majorant x s) (hasCompactSupport_majorant x s)
      zero_le_one (measurable_const.indicator (measurableSet_euclBall x ρ))
      (abs_le_majorant x zero_le_one (fun z => ?_) (fun z hz => ?_))
    · by_cases h : z ∈ euclBall x ρ <;> simp [h]
    · refine Set.indicator_of_notMem (fun h => ?_) _
      have h1 := (mem_euclBall_iff_sq x hρ z).1 h
      have h2 : ρ ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hρ.le hρs 2
      linarith
  have hc0 : 0 ≤ r ^ (2 * (d + 1)) * s ^ (2 * (d + 1)) := mul_nonneg (pow_nonneg hr.le _) (pow_nonneg hs.le _)

  have hEq : ∀ k, ∫ y, chartDens J A (fun z => annWeight r s d k (euclPot (z - x)))
        (fun _ : Fin (d + 1) => euclPot) y =
      ∫ y, chartDens J A (fun z => r ^ (2 * (d + 1)) * s ^ (2 * (d + 1)) *
          (radialTransform (d + 1) (hk k) (euclPot (z - x) / s ^ 2) -
            radialTransform (d + 1) (hk k) (euclPot (z - x) / r ^ 2)))
        (fun _ : Fin (d + 1) => logDistSq x) y := by
    intro k
    have hT : (∫ τ in (0 : ℝ)..s ^ 2, annWeight r s d k τ * (((d + 1 : ℕ) : ℝ) * τ ^ (d + 1 - 1))) = 0 := by
      have h := radialTransform_annWeight d hr hs k (s ^ 2)
      rw [div_self (pow_pos hs 2).ne', radialTransform_hk_of_one_le d k le_rfl,
        radialTransform_hk_of_one_le d k ((one_le_div hr2).2 hs2), sub_self, mul_zero] at h
      unfold radialTransform at h
      rw [annWeight_zero_of_le d hr hrs k le_rfl, zero_mul, zero_sub, neg_eq_zero] at h
      exact h
    have h := varRadialWeight x (annWeight r s d k) (pk k * r ^ 2) (s ^ 2) hJ hdim hAf
      (contDiff_annWeight d k) (mul_pos (pk_pos k) hr2) (fun t ht => annWeight_const d hr hrs k ht)
      (fun t ht => annWeight_zero_of_le d hr hrs k ht) hT
    have hw : (fun z => radialTransform (d + 1) (annWeight r s d k) (euclPot (z - x))) = fun z =>
        r ^ (2 * (d + 1)) * s ^ (2 * (d + 1)) * (radialTransform (d + 1) (hk k) (euclPot (z - x) / s ^ 2) -
          radialTransform (d + 1) (hk k) (euclPot (z - x) / r ^ 2)) :=
      funext fun z => radialTransform_annWeight d hr hs k _
    rw [h, hw]

  have hL : Tendsto (fun k => ∫ y, chartDens J A (fun z => annWeight r s d k (euclPot (z - x)))
        (fun _ : Fin (d + 1) => euclPot) y) atTop
      (𝓝 (r ^ (2 * (d + 1)) * (∫ y, chartDens J A ((euclBall x s).indicator fun _ => 1)
          (fun _ : Fin (d + 1) => euclPot) y) -
        s ^ (2 * (d + 1)) * ∫ y, chartDens J A ((euclBall x r).indicator fun _ => 1)
          (fun _ : Fin (d + 1) => euclPot) y)) := by
    have h := tendsto_integral_chartDens hCM hJ hdim hAf hφσ (continuous_majorant x s)
      (hasCompactSupport_majorant x s) (C := r ^ (2 * (d + 1)) + s ^ (2 * (d + 1)))
      (add_nonneg (pow_nonneg hr.le _) (pow_nonneg hs.le _))
      (w := fun k z => annWeight r s d k (euclPot (z - x)))
      (w' := fun z => r ^ (2 * (d + 1)) * (euclBall x s).indicator (fun _ => (1 : ℝ)) z -
        s ^ (2 * (d + 1)) * (euclBall x r).indicator (fun _ => (1 : ℝ)) z)
      (fun k => ((contDiff_annWeight d k).continuous.comp (continuous_distSq x)).measurable)
      (fun k => abs_le_majorant x (add_nonneg (pow_nonneg hr.le _) (pow_nonneg hs.le _))
        (fun z => abs_annWeight_le d hr hs k _) (fun z hz => annWeight_zero_of_le d hr hrs k hz))
      (fun z => ((tendsto_hk_indicator x hs z).const_mul _).sub ((tendsto_hk_indicator x hr z).const_mul _))
    have hlim : ∫ y, chartDens J A (fun z => r ^ (2 * (d + 1)) * (euclBall x s).indicator (fun _ => (1 : ℝ)) z -
          s ^ (2 * (d + 1)) * (euclBall x r).indicator (fun _ => (1 : ℝ)) z)
          (fun _ : Fin (d + 1) => euclPot) y =
        r ^ (2 * (d + 1)) * (∫ y, chartDens J A ((euclBall x s).indicator fun _ => 1)
          (fun _ : Fin (d + 1) => euclPot) y) -
        s ^ (2 * (d + 1)) * ∫ y, chartDens J A ((euclBall x r).indicator fun _ => 1)
          (fun _ : Fin (d + 1) => euclPot) y := by
      simp only [chartDens_sub' hAf]
      rw [integral_sub ((hball s hs le_rfl).const_mul _) ((hball r hr hrs).const_mul _), integral_const_mul,
        integral_const_mul]
    rw [← hlim]
    exact h

  have hφτ : ∀ k, SmoothNear (zeroSet J)
      ((fun _ => logDistSmooth x hr : Fin (d + 1) → (Fin n → ℂ) → ℝ) k) :=
    fun _ => smoothNear_of_contDiff (S := zeroSet J) (contDiff_logDistSmooth x hr)
  have hgerm : ∀ z : Fin n → ℂ, r ^ 2 / 4 < euclPot (z - x) → ∀ i : Fin (d + 1),
      (fun _ => logDistSq x : Fin (d + 1) → (Fin n → ℂ) → ℝ) i =ᶠ[𝓝 z]
        (fun _ => logDistSmooth x hr : Fin (d + 1) → (Fin n → ℂ) → ℝ) i :=
    fun z hz _ => (logDistSmooth_eventuallyEq x hr hz).symm
  have hloc : ∀ k y, chartDens J A (fun z => r ^ (2 * (d + 1)) * s ^ (2 * (d + 1)) *
        (radialTransform (d + 1) (hk k) (euclPot (z - x) / s ^ 2) -
          radialTransform (d + 1) (hk k) (euclPot (z - x) / r ^ 2)))
        (fun _ : Fin (d + 1) => logDistSq x) y =
      chartDens J A (fun z => r ^ (2 * (d + 1)) * s ^ (2 * (d + 1)) *
        (radialTransform (d + 1) (hk k) (euclPot (z - x) / s ^ 2) -
          radialTransform (d + 1) (hk k) (euclPot (z - x) / r ^ 2)))
        (fun _ : Fin (d + 1) => logDistSmooth x hr) y := by
    intro k y
    refine chartDens_congr_fun (fun z _ hz => hgerm z ?_) y
    by_contra hle
    replace hle := not_lt.1 hle
    apply hz
    have hp := half_le_pk k
    rw [radialTransform_diff_of_le d hr hrs k (distSq_nonneg x z) (by nlinarith), mul_zero]
  have hloc' : ∀ y, chartDens J A (fun z => r ^ (2 * (d + 1)) * s ^ (2 * (d + 1)) *
        (euclBall x s \ euclBall x r).indicator (fun _ => (1 : ℝ)) z)
        (fun _ : Fin (d + 1) => logDistSq x) y =
      chartDens J A (fun z => r ^ (2 * (d + 1)) * s ^ (2 * (d + 1)) *
        (euclBall x s \ euclBall x r).indicator (fun _ => (1 : ℝ)) z)
        (fun _ : Fin (d + 1) => logDistSmooth x hr) y := by
    intro y
    refine chartDens_congr_fun (fun z _ hz => hgerm z ?_) y
    by_contra hle
    replace hle := not_lt.1 hle
    apply hz
    rw [Set.indicator_of_notMem (fun h => h.2 ((mem_euclBall_iff_sq x hr z).2 (by linarith))), mul_zero]
  have hR : Tendsto (fun k => ∫ y, chartDens J A (fun z => r ^ (2 * (d + 1)) * s ^ (2 * (d + 1)) *
        (radialTransform (d + 1) (hk k) (euclPot (z - x) / s ^ 2) -
          radialTransform (d + 1) (hk k) (euclPot (z - x) / r ^ 2)))
        (fun _ : Fin (d + 1) => logDistSq x) y) atTop
      (𝓝 (r ^ (2 * (d + 1)) * s ^ (2 * (d + 1)) *
        ∫ y, chartDens J A ((euclBall x s \ euclBall x r).indicator fun _ => 1)
          (fun _ : Fin (d + 1) => logDistSq x) y)) := by
    have h := tendsto_integral_chartDens hCM hJ hdim hAf hφτ (continuous_majorant x s)
      (hasCompactSupport_majorant x s) (C := 2 * (r ^ (2 * (d + 1)) * s ^ (2 * (d + 1))))
      (by positivity)
      (w := fun k z => r ^ (2 * (d + 1)) * s ^ (2 * (d + 1)) *
        (radialTransform (d + 1) (hk k) (euclPot (z - x) / s ^ 2) -
          radialTransform (d + 1) (hk k) (euclPot (z - x) / r ^ 2)))
      (w' := fun z => r ^ (2 * (d + 1)) * s ^ (2 * (d + 1)) *
        (euclBall x s \ euclBall x r).indicator (fun _ => (1 : ℝ)) z)
      (fun k => (continuous_const.mul
        (((continuous_radialTransform d (hk k).continuous).comp ((continuous_distSq x).div_const _)).sub
          ((continuous_radialTransform d (hk k).continuous).comp
            ((continuous_distSq x).div_const _)))).measurable)
      (fun k => abs_le_majorant x (by positivity) (fun z => ?_)
        (fun z hz => by rw [radialTransform_diff_of_ge d hr hrs k hz, mul_zero]))
      (fun z => (tendsto_radialTransform_diff d x hr hrs z).const_mul _)
    · have hl : ∀ y, chartDens J A (fun z => r ^ (2 * (d + 1)) * s ^ (2 * (d + 1)) *
            (euclBall x s \ euclBall x r).indicator (fun _ => (1 : ℝ)) z)
            (fun _ : Fin (d + 1) => logDistSq x) y =
          r ^ (2 * (d + 1)) * s ^ (2 * (d + 1)) * chartDens J A
            ((euclBall x s \ euclBall x r).indicator fun _ => 1) (fun _ : Fin (d + 1) => logDistSq x) y :=
        fun y => chartDens_const_mul hAf _ _ _ y
      rw [← integral_const_mul]
      simp only [← hl, hloc', hloc]
      exact h
    · have h1 := abs_radialTransform_hk_le d k (div_nonneg (distSq_nonneg x z) (pow_pos hs 2).le)
      have h2 := abs_radialTransform_hk_le d k (div_nonneg (distSq_nonneg x z) hr2.le)
      rw [abs_mul, abs_of_nonneg hc0]
      have h3 := abs_sub (radialTransform (d + 1) (hk k) (euclPot (z - x) / s ^ 2))
        (radialTransform (d + 1) (hk k) (euclPot (z - x) / r ^ 2))
      nlinarith
  exact tendsto_nhds_unique hL (hR.congr fun k => (hEq k).symm)

theorem regMassNearSmall : RegMassNearSmall.Statement :=
  RegMassNearSmall.proof RegFormCompare.proof
    (RegBallMass.proof GroundTheory.Heights₂.Heights.AutoClose.RegFixedBallMass
      (RegLelongMono.proof
        (RegLelongAnnulus.proof
          (RegRadialWeight.proof GroundTheory.Heights₂.Heights.AutoClose.StokesOnChart
            HilbertSamuel.Closed.ChartMassCompact RadialPrimitive.proof MaDensLogPow.proof)
          HilbertSamuel.Closed.ChartMassCompact)
        RegLogDensNonneg.proof)
      RegDensNonneg.proof)
    (SmallSetBallCover.proof (SmallSetTubeVolume.proof (PrimeTubeVolume.proof
      (VarietyMassLower.proof (VarietyTangentGraphDense.proof IndefiniteRowSideFullHecke.ComplexSets.ZeroSetOpenMass.full)
        TangentGraphLowerDensity.proof
        (VarietyLelongMono.proof ComplexSets.LinearNoetherNormalization.proof
          (VarWirtinger.proof GroundTheory.Heights₂.Heights.AutoClose.DiscriminantSheetCover HilbertSamuel.Closed.MassFinite)
          (VarLelongMono.proof varLelongAnnulus)))
      HilbertSamuel.Closed.MassFinite)))

end

end GlobalTheory.CompanionTheory.VarLelong
