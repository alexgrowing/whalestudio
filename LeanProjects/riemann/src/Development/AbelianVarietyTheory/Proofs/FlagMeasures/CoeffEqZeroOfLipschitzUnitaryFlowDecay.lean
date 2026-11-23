import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqZeroOfExpDecayOfFourierEqZeroOnHalfLine
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralNonnegOfSums
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CauchySchwarz
open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.LipFlow

theorem herm {V : Type} [AddCommGroup V] [Module ℂ V] (I : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (h : ∀ x, 0 ≤ I x x) (x y : V) : (starRingEnd ℂ) (I y x) = I x y := by
  have him : ∀ x, (I x x).im = 0 := fun x => ((Complex.le_def.1 (h x)).2).symm
  have h1 := him (x + y)
  have h2 := him (x + Complex.I • y)
  have hx := him x
  have hy := him y
  simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
    smul_eq_mul, RingHom.id_apply, Complex.conj_I, Complex.add_im, Complex.add_re, Complex.mul_im,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im] at h1 h2
  apply Complex.ext
  · simp only [Complex.conj_re]; linarith
  · simp only [Complex.conj_im]; linarith

theorem cauchy {V : Type} [AddCommGroup V] [Module ℂ V] (I : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (h : ∀ x, 0 ≤ I x x) (x y : V) : ‖I x y‖ ^ 2 ≤ (I x x).re * (I y y).re := by
  first
  | exact @_root_.GlobalTheory.HermitianCauchySchwarz.main
  | exact _root_.GlobalTheory.HermitianCauchySchwarz.main
  | (apply _root_.GlobalTheory.HermitianCauchySchwarz.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.HermitianCauchySchwarz.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.HermitianCauchySchwarz.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.HermitianCauchySchwarz.main ..)

theorem integrable_exp_abs {e : ℝ} (he : 0 < e) :
    Integrable (fun s : ℝ => Real.exp (-(e * |s|))) := by
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0:ℝ))]
  refine IntegrableOn.union ?_ ?_
  · refine (integrableOn_exp_mul_Iic he 0).congr_fun (fun x hx => ?_) measurableSet_Iic
    simp only [abs_of_nonpos (Set.mem_Iic.1 hx)]
    congr 1; ring
  · refine (exp_neg_integrableOn_Ioi 0 he).congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp only [abs_of_pos (Set.mem_Ioi.1 hx)]
    congr 1; ring

theorem decay_shift {φ : ℝ → ℂ} {A e : ℝ} (he : 0 < e)
    (h : ∀ s, ‖φ s‖ ≤ A * Real.exp (-(e * |s|))) (r t : ℝ) :
    ‖φ (r + t)‖ ≤ A * Real.exp (e * |r|) * Real.exp (-(e * |t|)) := by
  have hA : 0 ≤ A := by
    have := (norm_nonneg _).trans (h 0)
    simpa using this
  refine (h _).trans ?_
  rw [mul_assoc, ← Real.exp_add]
  gcongr
  have : |t| ≤ |r| + |r + t| := by
    have := abs_sub (r + t) r
    simp only [add_sub_cancel_left] at this
    linarith
  nlinarith

theorem integrable_fourier {φ : ℝ → ℂ} (hc : Continuous φ) {A e : ℝ} (he : 0 < e)
    (h : ∀ s, ‖φ s‖ ≤ A * Real.exp (-(e * |s|))) (ξ : ℝ) :
    Integrable (fun s : ℝ => Complex.exp (-(Complex.I * ξ * s)) * φ s) := by
  refine ((integrable_exp_abs he).const_mul A).mono' (by fun_prop) (ae_of_all _ fun s => ?_)
  rw [norm_mul, Complex.norm_exp]
  simpa using h s

theorem fourier_shift (φ : ℝ → ℂ) (ξ r : ℝ) :
    ∫ s : ℝ, Complex.exp (-(Complex.I * ξ * s)) * φ (r + s)
      = Complex.exp (Complex.I * ξ * r) * ∫ s : ℝ, Complex.exp (-(Complex.I * ξ * s)) * φ s := by
  rw [← integral_const_mul,
    ← integral_add_left_eq_self (fun s : ℝ => Complex.exp (Complex.I * ξ * r) *
      (Complex.exp (-(Complex.I * ξ * s)) * φ s)) r]
  congr 1; funext s
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2; push_cast; ring

theorem coeff_eq_zero : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (I : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (U : ℝ → V →ₗ[ℂ] V) (C : ℝ) (v : V), (∀ x, 0 ≤ I x x) → U 0 = LinearMap.id → (∀ s t, U (s + t) = (U s).comp (U t)) → (∀ s x y, I (U s x) (U s y) = I x y) → (∀ s x, |s| ≤ 1 → (I (U s x - x) (U s x - x)).re ≤ C * s ^ 2 * (I x x).re) → (∃ A e : ℝ, 0 < e ∧ ∀ s, ‖I v (U s v)‖ ≤ A * Real.exp (-(e * |s|))) → I v v = 0 := by
  intro V _ _ I U C v hpos h0 hadd hiso hlip ⟨A, e, he, hdec⟩
  set φ : ℝ → ℂ := fun s => I v (U s v) with hφ
  have hU : ∀ s t x, U s (U t x) = U (s + t) x := fun s t x => by rw [hadd]; rfl
  have hre : ∀ x, 0 ≤ (I x x).re := fun x => (Complex.le_def.1 (hpos x)).1
  have him : ∀ x, (I x x).im = 0 := fun x => ((Complex.le_def.1 (hpos x)).2).symm
  have hcont : Continuous φ := by
    rw [continuous_iff_continuousAt]
    intro t
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have hb : ∀ᶠ u in nhds t, ‖φ u - φ t‖ ≤
        Real.sqrt ((I v v).re * (C * (u - t) ^ 2 * (I v v).re)) := by
      filter_upwards [Metric.closedBall_mem_nhds t one_pos] with u hu
      have hu' : |u - t| ≤ 1 := by simpa [Real.dist_eq] using hu
      apply Real.le_sqrt_of_sq_le
      have e1 : φ u - φ t = I v (U (u - t) (U t v) - U t v) := by
        simp [hφ, hU]
      rw [e1]
      refine (cauchy I hpos _ _).trans ?_
      have := hlip (u - t) (U t v) hu'
      rw [hiso] at this
      exact mul_le_mul_of_nonneg_left this (hre v)
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) hb ?_
    have : Continuous fun u : ℝ => Real.sqrt ((I v v).re * (C * (u - t) ^ 2 * (I v v).re)) := by
      fun_prop
    simpa using this.tendsto t
  have hsum : ∀ (k : ℕ) (t : Fin k → ℝ) (z : Fin k → ℂ) (r : ℝ),
      I (∑ i, z i • U (t i) v) (U r (∑ i, z i • U (t i) v))
        = ∑ i, ∑ j, star (z i) * z j * φ (r + (t j - t i)) := by
    intro k t z r
    rw [map_sum (U r), map_sum I, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : I (U (t i) v) (U r (U (t j) v)) = φ (r + (t j - t i)) := by
      simp only [hφ]
      rw [← hiso (t i) v (U (r + (t j - t i)) v), hU, hU]
      congr 3; ring
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, this]
    simp only [RCLike.star_def]
    ring
  have hφpos := GlobalTheory.PosDefFT.fourier_nonneg φ hcont ⟨A, e, he, hdec⟩ (fun k t z => by
    have := hsum k t z 0
    simp only [h0, LinearMap.id_apply, zero_add] at this
    rw [← this]; exact hpos _)
  have hzero : φ = 0 := by
    refine GlobalTheory.eq_zero_of_exp_decay_of_fourier_eq_zero_on_halfLine φ (Real.pi * (|C| + 1)) hcont ⟨A, e, he, hdec⟩ fun ξ hξ => ?_
    have hC : 0 ≤ |C| := abs_nonneg C
    have hξ0 : 0 < ξ := lt_of_lt_of_le (by positivity) hξ
    set s : ℝ := Real.pi / ξ with hs
    have hs0 : 0 < s := by positivity
    have hs1 : s * (|C| + 1) ≤ 1 := by
      rw [hs, div_mul_eq_mul_div, div_le_one hξ0]; exact hξ
    have hs2 : s ≤ 1 := by nlinarith
    have hCs : C * s ^ 2 ≤ 1 := by
      have := le_abs_self C
      nlinarith [mul_nonneg hC hs0.le]
    let ψ : ℝ → ℂ := fun t => ((C * s ^ 2 - 2 : ℝ) : ℂ) * φ t + φ (s + t) + φ (-s + t)
    have hψc : Continuous ψ := by fun_prop
    have hψd : ∀ t, ‖ψ t‖ ≤ (|C * s ^ 2 - 2| * A + A * Real.exp (e * |s|)
        + A * Real.exp (e * |-s|)) * Real.exp (-(e * |t|)) := by
      intro t
      have a1 := decay_shift he hdec s t
      have a2 := decay_shift he hdec (-s) t
      have a3 : ‖((C * s ^ 2 - 2 : ℝ) : ℂ) * φ t‖
          ≤ |C * s ^ 2 - 2| * (A * Real.exp (-(e * |t|))) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hdec t) (abs_nonneg _)
      refine (norm_add₃_le).trans ?_
      refine (add_le_add (add_le_add a3 a1) a2).trans (le_of_eq (by ring))
    have hψpos := GlobalTheory.PosDefFT.fourier_nonneg ψ hψc ⟨_, e, he, hψd⟩ (fun k t z => by
      set x := ∑ i, z i • U (t i) v with hx
      have b0 := hsum k t z 0
      have b1 := hsum k t z s
      have b2 := hsum k t z (-s)
      rw [← hx] at b0 b1 b2
      simp only [h0, LinearMap.id_apply, zero_add] at b0
      have b3 : I (U s x) x = I x (U (-s) x) := by
        rw [← hiso s x (U (-s) x), hU]; simp [h0]
      have b4 : ∑ i, ∑ j, star (z i) * z j * ψ (t j - t i)
          = ((C * s ^ 2 - 2 : ℝ) : ℂ) * I x x + I x (U s x) + I x (U (-s) x) := by
        rw [b0, b1, b2]
        simp only [ψ, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      have b5 : ((C * s ^ 2 - 2 : ℝ) : ℂ) * I x x + I x (U s x) + I x (U (-s) x)
          = ((C * s ^ 2 : ℝ) : ℂ) * I x x - I (U s x - x) (U s x - x) := by
        simp only [map_sub, LinearMap.sub_apply, hiso, b3]
        push_cast; ring
      rw [b4, b5, Complex.le_def]
      have := hlip s x (by rwa [abs_of_pos hs0])
      constructor
      · rw [Complex.sub_re, Complex.re_ofReal_mul]; simpa using this
      · rw [Complex.sub_im, Complex.im_ofReal_mul, him, him]; simp) ξ
    have i0 := integrable_fourier hcont he hdec ξ
    have i1 := integrable_fourier (φ := fun t => φ (s + t)) (by fun_prop) he
      (decay_shift he hdec s) ξ
    have i2 := integrable_fourier (φ := fun t => φ (-s + t)) (by fun_prop) he
      (decay_shift he hdec (-s)) ξ
    have hξs : Complex.I * ξ * s = Real.pi * Complex.I := by
      have : (ξ : ℂ) * s = Real.pi := by
        rw [← Complex.ofReal_mul, hs, mul_div_cancel₀ _ hξ0.ne']
      rw [← this]; ring
    have hF : ∫ t : ℝ, Complex.exp (-(Complex.I * ξ * t)) * ψ t
        = ((C * s ^ 2 - 4 : ℝ) : ℂ) * ∫ t : ℝ, Complex.exp (-(Complex.I * ξ * t)) * φ t := by
      have : (fun t : ℝ => Complex.exp (-(Complex.I * ξ * t)) * ψ t) = fun t : ℝ =>
          ((C * s ^ 2 - 2 : ℝ) : ℂ) * (Complex.exp (-(Complex.I * ξ * t)) * φ t)
          + Complex.exp (-(Complex.I * ξ * t)) * φ (s + t)
          + Complex.exp (-(Complex.I * ξ * t)) * φ (-s + t) := by
        funext t; simp only [ψ]; ring
      rw [this, integral_add (by exact (i0.const_mul _).add i1) i2, integral_add (i0.const_mul _) i1,
        integral_const_mul, fourier_shift, fourier_shift, hξs]
      have h2 : Complex.I * ξ * ((-s : ℝ) : ℂ) = -(Real.pi * Complex.I) := by
        rw [← hξs]; push_cast; ring
      rw [h2, Complex.exp_neg, Complex.exp_pi_mul_I]
      push_cast; ring
    rw [hF] at hψpos
    have p0 := hφpos ξ
    set F := ∫ t : ℝ, Complex.exp (-(Complex.I * ξ * t)) * φ t
    obtain ⟨p1, p2⟩ := Complex.le_def.1 p0
    have p3 := (Complex.le_def.1 hψpos).1
    rw [Complex.re_ofReal_mul] at p3
    simp only [Complex.zero_re, Complex.zero_im] at p1 p2 p3
    apply Complex.ext
    · simp only [Complex.zero_re]; nlinarith
    · simp [← p2]
  have := congrFun hzero 0
  simpa [hφ, h0] using this

end GlobalTheory.LipFlow
