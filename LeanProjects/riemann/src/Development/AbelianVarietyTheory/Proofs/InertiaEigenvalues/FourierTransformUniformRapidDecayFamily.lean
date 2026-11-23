import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped ComplexConjugate nonZeroDivisors ContDiff

noncomputable section

open Real Complex
open scoped FourierTransform

namespace GlobalTheory.FourierDecay

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}

def pairL (u : Fin n → Cinf E) : (Fin n → Cinf E) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => ∑ i, ∑ w, 2 * (x i w * u i w).re
      map_add' := fun x y => by
        simp only [Pi.add_apply, add_mul, Complex.add_re, mul_add, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        simp only [Pi.smul_apply, Complex.real_smul, mul_assoc, Complex.re_ofReal_mul, RingHom.id_apply,
          smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun w _ => by ring }

theorem pairL_apply (u x : Fin n → Cinf E) : pairL u x = ∑ i, ∑ w, 2 * (x i w * u i w).re := rfl

instance isAddHaarMeasure_volume : (volume : Measure (Fin n → Cinf E)).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure _

instance isAddHaarMeasure_infMeasure : (infMeasure E n).IsAddHaarMeasure :=
  Measure.IsAddHaarMeasure.smul _ (by simp) (by simp)

theorem hasFDerivAt_kernel (u x : Fin n → Cinf E) :
    HasFDerivAt (fun y => (𝐞 (-pairL u y) : ℂ))
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (2 * π * I * 𝐞 (-pairL u x))).comp (-pairL u)) x :=
  by
    have h1 := (Real.hasDerivAt_fourierChar (-pairL u x)).hasFDerivAt
    have h2 : HasFDerivAt (fun y => -pairL u y) (-pairL u) x := (pairL u).hasFDerivAt.neg
    exact h1.comp x h2

theorem fderiv_kernel (u x v : Fin n → Cinf E) :
    fderiv ℝ (fun y => (𝐞 (-pairL u y) : ℂ)) x v = -(2 * π * I * (pairL u v : ℂ)) * 𝐞 (-pairL u x) := by
  rw [(hasFDerivAt_kernel u x).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, Complex.real_smul]
  push_cast
  ring

theorem continuous_kernel (u : Fin n → Cinf E) : Continuous (fun y => (𝐞 (-pairL u y) : ℂ)) :=
  continuous_iff_continuousAt.2 fun x => (hasFDerivAt_kernel u x).continuousAt

theorem infFourier_fderiv {f : (Fin n → Cinf E) → ℂ} (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f)
    (v u : Fin n → Cinf E) :
    infFourier (fun y => fderiv ℝ f y v) u = (2 * π * I * (pairL u v : ℂ)) * infFourier f u := by
  have hfc : Continuous f := hf.continuous
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have hf'c : Continuous (fun y => fderiv ℝ f y v) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hf's : HasCompactSupport (fun y => fderiv ℝ f y v) :=
    (hs.fderiv (𝕜 := ℝ)).comp_left (g := fun L : (Fin n → Cinf E) →L[ℝ] ℂ => L v) rfl
  have hgc := continuous_kernel u
  have h1 : Integrable (fun x => fderiv ℝ f x v * (𝐞 (-pairL u x) : ℂ)) (infMeasure E n) :=
    (hf'c.mul hgc).integrable_of_hasCompactSupport hf's.mul_right
  have h2 : Integrable (fun x => f x * fderiv ℝ (fun y => (𝐞 (-pairL u y) : ℂ)) x v) (infMeasure E n) := by
    simp only [fderiv_kernel]
    exact (hfc.mul (continuous_const.mul hgc)).integrable_of_hasCompactSupport hs.mul_right
  have h3 : Integrable (fun x => f x * (𝐞 (-pairL u x) : ℂ)) (infMeasure E n) :=
    (hfc.mul hgc).integrable_of_hasCompactSupport hs.mul_right
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3 (fun x _ => hd x)
    (fun x _ => (hasFDerivAt_kernel u x).differentiableAt)
  simp only [fderiv_kernel] at key
  have e : ∫ x, f x * (-(2 * π * I * (pairL u v : ℂ)) * (𝐞 (-pairL u x) : ℂ)) ∂infMeasure E n =
      -(2 * π * I * (pairL u v : ℂ)) * ∫ x, f x * (𝐞 (-pairL u x) : ℂ) ∂infMeasure E n := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  show ∫ x, fderiv ℝ f x v * (𝐞 (-pairL u x) : ℂ) ∂infMeasure E n =
    (2 * π * I * (pairL u v : ℂ)) * ∫ x, f x * (𝐞 (-pairL u x) : ℂ) ∂infMeasure E n
  linear_combination key - e

open Classical in

def dirv (k : Fin n × InfinitePlace E × Bool) : Fin n → Cinf E :=
  Pi.single k.1 (Pi.single k.2.1 (if k.2.2 then I else 1))

theorem pairL_dirv (u : Fin n → Cinf E) (k : Fin n × InfinitePlace E × Bool) :
    pairL u (dirv k) = 2 * ((if k.2.2 then I else 1) * u k.1 k.2.1).re := by
  classical
  obtain ⟨i, w, b⟩ := k
  rw [pairL_apply, Finset.sum_eq_single i, Finset.sum_eq_single w]
  · simp [dirv]
  · intro w' _ hw
    simp [dirv, Pi.single_apply, hw]
  · simp
  · intro j _ hj
    simp [dirv, Pi.single_apply, hj]
  · simp

theorem norm_le_sum_pairL (u : Fin n → Cinf E) : ‖u‖ ≤ ∑ k, |pairL u (dirv k)| := by
  have hcoord : ∀ i w, ‖u i w‖ ≤ |pairL u (dirv (i, w, false))| + |pairL u (dirv (i, w, true))| := by
    intro i w
    rw [pairL_dirv, pairL_dirv]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul, Complex.I_mul_re, abs_mul, abs_neg, abs_two]
    have := Complex.norm_le_abs_re_add_abs_im (u i w)
    nlinarith [abs_nonneg (u i w).re, abs_nonneg (u i w).im]
  have hS : ∑ k, |pairL u (dirv k)| =
      ∑ i, ∑ w, (|pairL u (dirv (i, w, false))| + |pairL u (dirv (i, w, true))|) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Fintype.sum_bool]
    ring
  rw [hS]
  have h0 : 0 ≤ ∑ i, ∑ w, (|pairL u (dirv (i, w, false))| + |pairL u (dirv (i, w, true))|) := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun w => ?_
  refine (hcoord i w).trans ?_
  have hi := Finset.single_le_sum (f := fun i => ∑ w, (|pairL u (dirv (i, w, false))| + |pairL u (dirv (i, w, true))|))
    (fun i _ => by positivity) (Finset.mem_univ i)
  have hw := Finset.single_le_sum (f := fun w => (|pairL u (dirv (i, w, false))| + |pairL u (dirv (i, w, true))|))
    (fun w _ => by positivity) (Finset.mem_univ w)
  exact hw.trans hi

end GlobalTheory.FourierDecay

open GlobalTheory.FourierDecay in

theorem GlobalTheory.fourier_decay_family : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (ι : Type)
    (w : ι → ℝ) (𝒞 : Set (ι → (Fin n → Cinf E) → ℂ)),
    (∀ f ∈ 𝒞, (∀ i, ContDiff ℝ ∞ (f i) ∧ HasCompactSupport (f i)) ∧ ∃ C : ℝ, ∀ i, ∫ y, ‖f i y‖ ∂(infMeasure E n) ≤ C * w i) →
    (∀ f ∈ 𝒞, ∀ v : Fin n → Cinf E, (fun i y => fderiv ℝ (f i) y v) ∈ 𝒞) →
    ∀ M : ℕ, ∀ f ∈ 𝒞, ∃ C : ℝ, ∀ i u, ‖infFourier (f i) u‖ * (1 + ‖u‖) ^ M ≤ C * w i := by
  intro E _ _ _ n ι w 𝒞 hC hD M
  induction M with
  | zero =>
    intro f hf
    obtain ⟨C, hC'⟩ := (hC f hf).2
    refine ⟨C, fun i u => ?_⟩
    rw [pow_zero, mul_one]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq_of_le ?_ (hC' i))
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ‖f i x * _‖ = ‖f i x‖
    rw [norm_mul, Circle.norm_coe, mul_one]
  | succ M ih =>
    intro f hf
    choose C hC' using fun k : Fin n × InfinitePlace E × Bool => ih _ (hD f hf (dirv k))
    obtain ⟨C₀, h₀⟩ := ih f hf
    refine ⟨C₀ + ∑ k, C k / (2 * π), fun i u => ?_⟩
    obtain ⟨hsm, hcs⟩ := (hC f hf).1 i
    have hrel : ∀ k, ‖infFourier (f i) u‖ * (1 + ‖u‖) ^ M * |pairL u (dirv k)| =
        ‖infFourier (fun y => fderiv ℝ (f i) y (dirv k)) u‖ * (1 + ‖u‖) ^ M / (2 * π) := by
      intro k
      rw [infFourier_fderiv hsm hcs, norm_mul]
      have : ‖(2 * π * I * (pairL u (dirv k) : ℂ))‖ = 2 * π * |pairL u (dirv k)| := by
        simp [norm_mul, Complex.norm_real, abs_of_pos pi_pos]
      rw [this]
      field_simp
    have hN := norm_le_sum_pairL u
    have hA : 0 ≤ ‖infFourier (f i) u‖ * (1 + ‖u‖) ^ M := by positivity
    calc ‖infFourier (f i) u‖ * (1 + ‖u‖) ^ (M + 1)
        = ‖infFourier (f i) u‖ * (1 + ‖u‖) ^ M + ‖infFourier (f i) u‖ * (1 + ‖u‖) ^ M * ‖u‖ := by ring
      _ ≤ ‖infFourier (f i) u‖ * (1 + ‖u‖) ^ M + ‖infFourier (f i) u‖ * (1 + ‖u‖) ^ M * ∑ k, |pairL u (dirv k)| :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hN hA)
      _ = ‖infFourier (f i) u‖ * (1 + ‖u‖) ^ M +
            ∑ k, ‖infFourier (fun y => fderiv ℝ (f i) y (dirv k)) u‖ * (1 + ‖u‖) ^ M / (2 * π) := by
          rw [Finset.mul_sum]
          exact congrArg _ (Finset.sum_congr rfl fun k _ => hrel k)
      _ ≤ C₀ * w i + ∑ k, C k * w i / (2 * π) :=
          add_le_add (h₀ i u) (Finset.sum_le_sum fun k _ => div_le_div_of_nonneg_right (hC' k i u) (by positivity))
      _ = (C₀ + ∑ k, C k / (2 * π)) * w i := by
          rw [add_mul, Finset.sum_mul]
          congr 1
          exact Finset.sum_congr rfl fun k _ => by ring
