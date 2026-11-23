import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
open MeasureTheory

noncomputable section

namespace GlobalTheory.GaussPairing

open Metric Filter Topology

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

def evalDiag (x : V) : (V →L[ℝ] V →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.apply ℝ ℂ x).comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] ℂ) x)

@[simp] theorem evalDiag_apply (x : V) (B : V →L[ℝ] V →L[ℝ] ℂ) : evalDiag x B = B x x := rfl

theorem norm_evalDiag_le (x : V) : ‖evalDiag x‖ ≤ ‖x‖ * ‖x‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (fun B => (B.le_opNorm₂ x x).trans_eq (by ring))

theorem continuous_evalDiag : Continuous (evalDiag (V := V)) :=
  continuous_clm_apply.2 fun B => by simpa using B.continuous.clm_apply continuous_id

def diagProd (ys : List (V →L[ℝ] V →L[ℝ] ℂ)) (x : V) : ℂ := (ys.map fun y => y x x).prod

theorem continuous_diagProd (ys : List (V →L[ℝ] V →L[ℝ] ℂ)) : Continuous (diagProd ys) :=
  continuous_list_prod ys fun y _ => y.continuous.clm_apply continuous_id

theorem prod_norm_nonneg (ys : List (V →L[ℝ] V →L[ℝ] ℂ)) : 0 ≤ (ys.map (‖·‖)).prod :=
  List.prod_nonneg (by simp)

theorem norm_diagProd_le (ys : List (V →L[ℝ] V →L[ℝ] ℂ)) (x : V) :
    ‖diagProd ys x‖ ≤ (ys.map (‖·‖)).prod * ‖x‖ ^ (2 * ys.length) := by
  induction ys with
  | nil => simp [diagProd]
  | cons y ys ih =>
    simp only [diagProd, List.map_cons, List.prod_cons, List.length_cons] at ih ⊢
    rw [norm_mul]
    have h0 := prod_norm_nonneg ys
    calc ‖y x x‖ * ‖(ys.map fun y => y x x).prod‖
        ≤ (‖y‖ * ‖x‖ * ‖x‖) * ((ys.map (‖·‖)).prod * ‖x‖ ^ (2 * ys.length)) :=
          mul_le_mul (y.le_opNorm₂ x x) ih (norm_nonneg _) (by positivity)
      _ = _ := by ring

def negDef : Set (V →L[ℝ] V →L[ℝ] ℂ) := {B | ∃ ε > 0, ∀ x, (B x x).re ≤ -(ε * ‖x‖ ^ 2)}

theorem re_le_of_norm_sub_le {B B' : V →L[ℝ] V →L[ℝ] ℂ} {ε : ℝ}
    (hB : ∀ x, (B x x).re ≤ -(ε * ‖x‖ ^ 2)) (hB' : ‖B' - B‖ ≤ ε / 2) (x : V) :
    (B' x x).re ≤ -(ε / 2 * ‖x‖ ^ 2) := by
  have h1 : (B' x x).re = (B x x).re + ((B' - B) x x).re := by simp
  have h2 : ((B' - B) x x).re ≤ ε / 2 * ‖x‖ ^ 2 := by
    calc ((B' - B) x x).re ≤ ‖(B' - B) x x‖ := Complex.re_le_norm _
      _ ≤ ‖B' - B‖ * ‖x‖ * ‖x‖ := (B' - B).le_opNorm₂ x x
      _ ≤ ε / 2 * ‖x‖ * ‖x‖ := by gcongr
      _ = ε / 2 * ‖x‖ ^ 2 := by ring
  rw [h1]; linarith [hB x]

theorem isOpen_negDef : IsOpen (negDef (V := V)) := by
  rw [Metric.isOpen_iff]
  rintro B ⟨ε, hε, hB⟩
  refine ⟨ε / 2, by positivity, fun B' hB' => ⟨ε / 2, by positivity, re_le_of_norm_sub_le hB ?_⟩⟩
  rw [mem_ball, dist_eq_norm] at hB'
  exact hB'.le

variable [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]

theorem integrable_norm_pow_mul_exp (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : V => ‖x‖ ^ n * Real.exp (-b * ‖x‖ ^ 2)) μ := by
  rcases subsingleton_or_nontrivial V with h | h
  · exact Integrable.of_finite
  rw [integrable_fun_norm_addHaar μ (f := fun r => r ^ n * Real.exp (-b * r ^ 2))]
  have := integrableOn_rpow_mul_exp_neg_mul_sq hb
    (s := ((Module.finrank ℝ V - 1 + n : ℕ) : ℝ)) (lt_of_lt_of_le neg_one_lt_zero (by positivity))
  refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast, smul_eq_mul, pow_add, mul_assoc]

def gaussMoment (ys : List (V →L[ℝ] V →L[ℝ] ℂ)) (B : V →L[ℝ] V →L[ℝ] ℂ) : ℂ :=
  ∫ x, Complex.exp (B x x) * diagProd ys x ∂μ

omit [MeasurableSpace V] [BorelSpace V] in
theorem norm_integrand_le {B : V →L[ℝ] V →L[ℝ] ℂ} {ε : ℝ} (hB : ∀ x, (B x x).re ≤ -(ε * ‖x‖ ^ 2))
    (ys : List (V →L[ℝ] V →L[ℝ] ℂ)) (x : V) :
    ‖Complex.exp (B x x) * diagProd ys x‖ ≤
      (ys.map (‖·‖)).prod * (‖x‖ ^ (2 * ys.length) * Real.exp (-ε * ‖x‖ ^ 2)) := by
  rw [norm_mul, Complex.norm_exp]
  have h0 := prod_norm_nonneg ys
  calc Real.exp (B x x).re * ‖diagProd ys x‖
      ≤ Real.exp (-ε * ‖x‖ ^ 2) * ((ys.map (‖·‖)).prod * ‖x‖ ^ (2 * ys.length)) :=
        mul_le_mul (Real.exp_le_exp.2 (by linarith [hB x])) (norm_diagProd_le ys x) (norm_nonneg _)
          (Real.exp_pos _).le
    _ = _ := by ring

theorem continuous_integrand (B : V →L[ℝ] V →L[ℝ] ℂ) (ys : List (V →L[ℝ] V →L[ℝ] ℂ)) :
    Continuous fun x => Complex.exp (B x x) * diagProd ys x :=
  (Complex.continuous_exp.comp (B.continuous.clm_apply continuous_id)).mul (continuous_diagProd ys)

theorem integrable_integrand {B : V →L[ℝ] V →L[ℝ] ℂ} {ε : ℝ} (hε : 0 < ε)
    (hB : ∀ x, (B x x).re ≤ -(ε * ‖x‖ ^ 2)) (ys : List (V →L[ℝ] V →L[ℝ] ℂ)) :
    Integrable (fun x => Complex.exp (B x x) * diagProd ys x) μ :=
  ((integrable_norm_pow_mul_exp μ _ hε).const_mul _).mono'
    (continuous_integrand B ys).aestronglyMeasurable (Eventually.of_forall (norm_integrand_le hB ys))

def integrandDeriv (ys : List (V →L[ℝ] V →L[ℝ] ℂ)) (B : V →L[ℝ] V →L[ℝ] ℂ) (x : V) :
    (V →L[ℝ] V →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (Complex.exp (B x x) * diagProd ys x) • evalDiag x

theorem hasFDerivAt_integrand (ys : List (V →L[ℝ] V →L[ℝ] ℂ)) (B : V →L[ℝ] V →L[ℝ] ℂ) (x : V) :
    HasFDerivAt (fun B' : V →L[ℝ] V →L[ℝ] ℂ => Complex.exp (B' x x) * diagProd ys x)
      (integrandDeriv ys B x) B := by
  have := ((evalDiag x).hasFDerivAt (x := B)).cexp.mul_const (diagProd ys x)
  refine this.congr_fderiv ?_
  ext B'
  simp [integrandDeriv]
  try ring

theorem norm_integrandDeriv_le {B : V →L[ℝ] V →L[ℝ] ℂ} {ε : ℝ}
    (hB : ∀ x, (B x x).re ≤ -(ε * ‖x‖ ^ 2)) (ys : List (V →L[ℝ] V →L[ℝ] ℂ)) (x : V) :
    ‖integrandDeriv ys B x‖ ≤
      (ys.map (‖·‖)).prod * (‖x‖ ^ (2 * ys.length + 2) * Real.exp (-ε * ‖x‖ ^ 2)) := by
  rw [integrandDeriv, norm_smul]
  calc ‖Complex.exp (B x x) * diagProd ys x‖ * ‖evalDiag x‖
      ≤ ((ys.map (‖·‖)).prod * (‖x‖ ^ (2 * ys.length) * Real.exp (-ε * ‖x‖ ^ 2))) * (‖x‖ * ‖x‖) :=
        mul_le_mul (norm_integrand_le hB ys x) (norm_evalDiag_le x) (norm_nonneg _)
          (by have := prod_norm_nonneg ys; positivity)
    _ = _ := by ring

theorem integrable_integrandDeriv {B : V →L[ℝ] V →L[ℝ] ℂ} {ε : ℝ} (hε : 0 < ε)
    (hB : ∀ x, (B x x).re ≤ -(ε * ‖x‖ ^ 2)) (ys : List (V →L[ℝ] V →L[ℝ] ℂ)) :
    Integrable (integrandDeriv ys B) μ :=
  ((integrable_norm_pow_mul_exp μ _ hε).const_mul _).mono'
    (((continuous_integrand B ys).smul continuous_evalDiag).aestronglyMeasurable)
    (Eventually.of_forall (norm_integrandDeriv_le hB ys))

theorem hasFDerivAt_gaussMoment (ys : List (V →L[ℝ] V →L[ℝ] ℂ)) {B : V →L[ℝ] V →L[ℝ] ℂ}
    (hB : B ∈ negDef) :
    HasFDerivAt (gaussMoment μ ys) (∫ x, integrandDeriv ys B x ∂μ) B := by
  obtain ⟨ε, hε, hBε⟩ := hB
  have hball : ∀ B' ∈ ball B (ε / 2), ∀ x, (B' x x).re ≤ -(ε / 2 * ‖x‖ ^ 2) := fun B' hB' =>
    re_le_of_norm_sub_le hBε (by rw [mem_ball, dist_eq_norm] at hB'; exact hB'.le)
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun B' x => Complex.exp (B' x x) * diagProd ys x)
    (ball_mem_nhds B (by positivity : 0 < ε / 2))
    (bound := fun x => (ys.map (‖·‖)).prod *
      (‖x‖ ^ (2 * ys.length + 2) * Real.exp (-(ε / 2) * ‖x‖ ^ 2)))
    (Eventually.of_forall fun B' => (continuous_integrand B' ys).aestronglyMeasurable)
    (integrable_integrand μ hε hBε ys)
    (integrable_integrandDeriv μ hε hBε ys).aestronglyMeasurable
    (Eventually.of_forall fun x B' hB' => norm_integrandDeriv_le (hball B' hB') ys x)
    ((integrable_norm_pow_mul_exp μ _ (by positivity)).const_mul _)
    (Eventually.of_forall fun x B' _ => hasFDerivAt_integrand ys B' x)

theorem fderiv_gaussMoment_apply (ys : List (V →L[ℝ] V →L[ℝ] ℂ)) {B : V →L[ℝ] V →L[ℝ] ℂ}
    (hB : B ∈ negDef) (y : V →L[ℝ] V →L[ℝ] ℂ) :
    fderiv ℝ (gaussMoment μ ys) B y = gaussMoment μ (y :: ys) B := by
  obtain ⟨ε, hε, hBε⟩ := id hB
  rw [(hasFDerivAt_gaussMoment μ ys hB).fderiv,
    ContinuousLinearMap.integral_apply (integrable_integrandDeriv μ hε hBε ys)]
  unfold gaussMoment
  congr 1
  funext x
  simp only [integrandDeriv, diagProd, ContinuousLinearMap.smul_apply, evalDiag_apply, smul_eq_mul,
    List.map_cons, List.prod_cons]
  ring

theorem contDiffOn_gaussMoment (n : ℕ) :
    ∀ ys : List (V →L[ℝ] V →L[ℝ] ℂ), ContDiffOn ℝ n (gaussMoment μ ys) negDef := by
  induction n with
  | zero =>
    intro ys
    exact contDiffOn_zero.2 fun B hB =>
      (hasFDerivAt_gaussMoment μ ys hB).continuousAt.continuousWithinAt
  | succ n ih =>
    intro ys
    have := contDiffOn_succ_of_fderiv_apply (n := (n : WithTop ℕ∞)) (f := gaussMoment μ ys)
      (s := negDef)
      (fun B hB => (hasFDerivAt_gaussMoment μ ys hB).differentiableAt.differentiableWithinAt)
      (fun h => by simp at h)
      (fun y => (ih (y :: ys)).congr fun B hB => by
        rw [fderivWithin_of_isOpen isOpen_negDef hB, fderiv_gaussMoment_apply μ ys hB])
    exact_mod_cast this

omit [MeasurableSpace V] [BorelSpace V] in

def toCont (N : V →ₗ[ℝ] V →ₗ[ℝ] ℂ) : V →L[ℝ] V →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℂ) ≃ₗ[ℝ] (V →L[ℝ] ℂ)).toLinearMap ∘ₗ N)

omit [MeasurableSpace V] [BorelSpace V] in
@[simp] theorem toCont_apply (N : V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (x y : V) : toCont N x y = N x y := rfl

omit [MeasurableSpace V] [BorelSpace V] in

def pairForm (M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (p : ℝ × ℝ) : V →L[ℝ] V →L[ℝ] ℂ :=
  toCont (M p.1 + (M p.2).compr₂ (Complex.conjAe.toLinearMap))

omit [MeasurableSpace V] [BorelSpace V] in
@[simp] theorem pairForm_apply (M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (p : ℝ × ℝ) (x y : V) :
    pairForm M p x y = M p.1 x y + starRingEnd ℂ (M p.2 x y) := by
  simp [pairForm]

theorem gauss_pairing_smooth_ne_zero (M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ)
    (hM : ∀ x y, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => M t x y)
    (hneg : ∀ t₀ : ℝ, ∃ ε > 0, ∀ᶠ t in nhds t₀, ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ =>
      ∫ x, Complex.exp (M p.1 x x) * starRingEnd ℂ (Complex.exp (M p.2 x x)) ∂μ) ∧
    ∀ u, ∫ x, Complex.exp (M u x x) * starRingEnd ℂ (Complex.exp (M u x x)) ∂μ ≠ 0 := by
  have hneg' : ∀ t, ∃ ε > 0, ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2) := fun t => by
    obtain ⟨ε, hε, h⟩ := hneg t
    exact ⟨ε, hε, h.self_of_nhds⟩
  constructor
  · have hP : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pairForm M) := by
      rw [contDiff_clm_apply_iff]
      intro x
      rw [contDiff_clm_apply_iff]
      intro y
      simp only [pairForm_apply]
      exact ((hM x y).comp contDiff_fst).add
        (Complex.conjCLE.contDiff.comp ((hM x y).comp contDiff_snd))
    have hmem : ∀ p, pairForm M p ∈ negDef := fun p => by
      obtain ⟨ε₁, h₁, hb₁⟩ := hneg' p.1
      obtain ⟨ε₂, h₂, hb₂⟩ := hneg' p.2
      refine ⟨ε₁ + ε₂, by positivity, fun x => ?_⟩
      simp only [pairForm_apply, Complex.add_re, Complex.conj_re]
      linarith [hb₁ x, hb₂ x]
    have heq : (fun p : ℝ × ℝ =>
        ∫ x, Complex.exp (M p.1 x x) * starRingEnd ℂ (Complex.exp (M p.2 x x)) ∂μ) =
        gaussMoment μ [] ∘ pairForm M := by
      funext p
      simp only [Function.comp, gaussMoment, diagProd, List.map_nil, List.prod_nil, mul_one,
        pairForm_apply]
      congr 1
      funext x
      rw [← Complex.exp_conj, ← Complex.exp_add]
    rw [heq]
    exact contDiff_infty.2 fun n =>
      (contDiffOn_gaussMoment μ n []).comp_contDiff (contDiff_infty.1 hP n) hmem
  · intro u
    obtain ⟨ε, hε, hb⟩ := hneg' u
    have hpt : ∀ x, Complex.exp (M u x x) * starRingEnd ℂ (Complex.exp (M u x x)) =
        ((Real.exp (2 * (M u x x).re) : ℝ) : ℂ) := fun x => by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp, sq, ← Real.exp_add,
        two_mul]
    simp only [hpt]
    rw [integral_complex_ofReal, Complex.ofReal_ne_zero]
    have hc : Continuous fun x => M u x x := (toCont (M u)).continuous.clm_apply continuous_id
    refine (integral_exp_pos ?_).ne'
    refine (integrable_norm_pow_mul_exp μ 0 (by positivity : 0 < 2 * ε)).mono'
      ((Real.continuous_exp.comp (continuous_const.mul
        (Complex.continuous_re.comp hc))).aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), pow_zero, one_mul]
    exact Real.exp_le_exp.2 (by linarith [hb x])

end GlobalTheory.GaussPairing
