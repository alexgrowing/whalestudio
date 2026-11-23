import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DTermOrigin
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization

noncomputable section

open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
open scoped ContDiff

namespace GlobalTheory.WeightTwoSum

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

def risingS (σ : ℂ) (m : I → ℕ) : ℂ := ∏ i, ((-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), (2 + σ + j))

def eTerm (φ : I → E →+* ℂ) (m : I → ℕ) (σ : ℂ) (z : I → ℂ) (x : E) : ℂ :=
  ∏ i, (((-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), (2 + σ + j)) * (starRingEnd ℂ (φ i x)) ^ m i *
    (defCoord φ z x i)⁻¹ ^ (2 + m i) * ((‖defCoord φ z x i‖ : ℝ) : ℂ) ^ (-2 * σ))

def dz (j : I) : (I → ℂ) →L[ℝ] ℂ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : I => ℂ) j

def dzbar (j : I) : (I → ℂ) →L[ℝ] ℂ := (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (dz j)

def homFac (z : I → ℂ) : ℂ := ∏ i, ((1 + z i) / (2 * (Real.pi : ℂ) * Complex.I))

def logFac (z : I → ℂ) : ℂ := ((Real.log (Complex.normSq (homFac z)) : ℝ) : ℂ)

def modPt {Φ : Type} (φ : I → E →+* ℂ) (e : I ≃ Φ) (θ : E) (z : I → ℂ) : Φ → ℂ :=
  fun τ => defCoord φ z θ (e.symm τ) / (1 + z (e.symm τ))

@[simp] theorem dz_apply (j : I) (v : I → ℂ) : dz j v = v j := rfl

@[simp] theorem dzbar_apply (j : I) (v : I → ℂ) : dzbar j v = starRingEnd ℂ (v j) := rfl

theorem eTerm_zero (φ : I → E →+* ℂ) (σ : ℂ) (z : I → ℂ) (x : E) : eTerm φ 0 σ z x = defTerm φ 2 z σ x := by
  simp [eTerm, defTerm]

theorem eTerm_origin (φ : I → E →+* ℂ) (m : I → ℕ) (σ : ℂ) (x : E) :
    eTerm φ m σ 0 x = risingS σ m * term φ 2 m σ x := by
  unfold eTerm risingS term
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [defCoord, Pi.zero_apply, zero_mul, add_zero]
  ring

theorem risingS_zero (m : I → ℕ) : risingS 0 m = risingFactor 2 m := by
  simp [risingS, risingFactor]

theorem differentiable_risingS (m : I → ℕ) : Differentiable ℂ fun σ => risingS σ m := by
  unfold risingS
  fun_prop

theorem isOpen_polydisc (I : Type) [Fintype I] : IsOpen (polydisc I) := by
  have : polydisc I = ⋂ i : I, {z : I → ℂ | ‖z i‖ < 1} := by
    ext z; simp [polydisc]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i).norm continuous_const

omit [Fintype I] in
theorem one_add_ne_zero {z : I → ℂ} (hz : z ∈ polydisc I) (i : I) : 1 + z i ≠ 0 := by
  intro h
  have h1 : z i = -1 := by linear_combination h
  have h2 := hz i
  rw [h1] at h2
  simp at h2

theorem homFac_ne_zero {z : I → ℂ} (hz : z ∈ polydisc I) : homFac z ≠ 0 := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  exact Finset.prod_ne_zero_iff.2 fun i _ => div_ne_zero (one_add_ne_zero hz i)
    (mul_ne_zero (mul_ne_zero two_ne_zero hπ) Complex.I_ne_zero)

theorem contDiff_homFac : ContDiff ℂ ∞ (homFac : (I → ℂ) → ℂ) := by
  unfold homFac
  exact contDiff_prod fun i _ => (contDiff_const.add (contDiff_apply ℂ ℂ i)).div_const _

theorem contDiffOn_logFac : ContDiffOn ℝ ∞ (logFac : (I → ℂ) → ℂ) (polydisc I) := by
  have h1 : ContDiff ℝ ∞ (homFac : (I → ℂ) → ℂ) := contDiff_homFac.restrict_scalars ℝ
  have h2 : ContDiff ℝ ∞ (fun z : I → ℂ => Complex.normSq (homFac z)) := by
    simp only [Complex.normSq_apply]
    exact ((Complex.reCLM.contDiff.comp h1).mul (Complex.reCLM.contDiff.comp h1)).add
      ((Complex.imCLM.contDiff.comp h1).mul (Complex.imCLM.contDiff.comp h1))
  have h3 : ContDiffOn ℝ ∞ (fun z : I → ℂ => Real.log (Complex.normSq (homFac z))) (polydisc I) :=
    h2.contDiffOn.log fun z hz => (Complex.normSq_pos.2 (homFac_ne_zero hz)).ne'
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn h3

theorem contDiffOn_modPt {Φ : Type} [Fintype Φ] (φ : I → E →+* ℂ) (e : I ≃ Φ) (θ : E) :
    ContDiffOn ℂ ∞ (modPt φ e θ) (polydisc I) := by
  refine contDiffOn_pi.2 fun τ => ?_
  unfold modPt defCoord
  refine ContDiffOn.div ?_ ?_ fun z hz => one_add_ne_zero hz _
  · exact (contDiff_const.add ((contDiff_apply ℂ ℂ _).mul contDiff_const)).contDiffOn
  · exact (contDiff_const.add (contDiff_apply ℂ ℂ _)).contDiffOn

omit [Fintype I] in

theorem modPt_im_pos {Φ : Type} (φ : I → E →+* ℂ) (e : I ≃ Φ) (θ : E) (hθ : ∀ i, 0 < (φ i θ).im)
    {z : I → ℂ} (hz : z ∈ polydisc I) (τ : Φ) : 0 < (modPt φ e θ z τ).im := by
  unfold modPt defCoord
  set i := e.symm τ
  have h0 : 0 < Complex.normSq (1 + z i) := Complex.normSq_pos.2 (one_add_ne_zero hz i)
  have h1 : Complex.normSq (z i) < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    have := hz i
    nlinarith [norm_nonneg (z i)]
  rw [Complex.div_im, ← sub_div]
  refine div_pos ?_ h0
  rw [Complex.normSq_apply] at h1
  have h2 := hθ i
  simp only [Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.one_re,
    Complex.one_im]
  nlinarith [mul_pos h2 (sub_pos.2 h1)]

example (φ : E →+* ℂ) (x : E) :
    eTerm (fun _ : Unit => φ) (fun _ => 1) 0 0 x = -2 * (starRingEnd ℂ (φ x)) * (φ x)⁻¹ ^ 3 := by
  simp [eTerm, defCoord]

end GlobalTheory.WeightTwoSum
