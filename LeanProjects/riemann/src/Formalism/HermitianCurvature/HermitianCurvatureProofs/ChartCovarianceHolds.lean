import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartEqsOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaFiniteOfHaar
import Formalism.FormalDegreeBessel.FinalG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity.ChartCovPf

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

def bq (H : B.Mat k r) : B.Mat k r →ₗ[ℝ] B.Mat k r →ₗ[ℝ] B.Mat k r :=
  LinearMap.mk₂ ℝ (fun M N => Mᴴ * H * N)
    (fun M M' N => by simp [Matrix.conjTranspose_add, Matrix.add_mul])
    (fun c M N => by simp [Matrix.conjTranspose_smul])
    (fun M N N' => by simp [Matrix.mul_add])
    (fun c M N => by simp)

def bqL (H : B.Mat k r) : B.Mat k r →L[ℝ] B.Mat k r →L[ℝ] B.Mat k r :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (B.Mat k r →ₗ[ℝ] B.Mat k r) ≃ₗ[ℝ] (B.Mat k r →L[ℝ] B.Mat k r)).toLinearMap ∘ₗ
      bq H)

theorem bqL_apply (H M N : B.Mat k r) : bqL H M N = Mᴴ * H * N := rfl

theorem tangent_eq {d : ℕ} {O : Set (Fin d → ℝ)} {κ : (Fin d → ℝ) → B.Mat k r} (hO : IsOpen O)
    (hκ : ContDiffOn ℝ ∞ κ O) (hG : ∀ y ∈ O, κ y ∈ B.GV k r) {x : Fin d → ℝ} (hx : x ∈ O)
    (v : Fin d → ℝ) :
    (fderiv ℝ κ x v)ᴴ * Hpk k r * κ x + (κ x)ᴴ * Hpk k r * fderiv ℝ κ x v = 0 := by
  have hd : DifferentiableAt ℝ κ x := (hκ.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hl : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hc := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have hB := (bqL (Hpk k r)).hasDerivAt_of_bilinear (fun _ => hc) (fun _ => hc)
  have hmem : ∀ᶠ t in nhds (0 : ℝ), x + t • v ∈ O := by
    have hcont : Continuous (fun t : ℝ => x + t • v) := by fun_prop
    exact hcont.continuousAt.preimage_mem_nhds (by simpa using hO.mem_nhds hx)
  have hev : (fun _ : ℝ => Hpk k r) =ᶠ[nhds 0]
      fun t : ℝ => bqL (Hpk k r) ((κ ∘ fun t : ℝ => x + t • v) t) ((κ ∘ fun t : ℝ => x + t • v) t) := by
    filter_upwards [hmem] with t ht
    rw [bqL_apply]
    exact (hG _ ht).symm
  have h2 := hB.congr_of_eventuallyEq hev
  have e := h2.deriv
  rw [deriv_const] at e
  simp only [Function.comp_apply, zero_smul, add_zero] at e
  have e' : (κ x)ᴴ * Hpk k r * fderiv ℝ κ x v + (fderiv ℝ κ x v)ᴴ * Hpk k r * κ x = 0 := e.symm
  exact (add_comm _ _).trans e'

theorem chart_id {d : ℕ} {O : Set (Fin d → ℝ)} {U : Set (B.Mat k r)} {κ : (Fin d → ℝ) → B.Mat k r}
    {Φ : B.Mat k r → (Fin d → ℝ)} (hC : IsChart k r d O U κ Φ) {x : Fin d → ℝ} (hx : x ∈ O) (v : Fin d → ℝ) :
    fderiv ℝ Φ (κ x) (fderiv ℝ κ x v) = v := by
  obtain ⟨hO, hU, hκ, hΦ, hκO, _⟩ := hC
  have hd : DifferentiableAt ℝ κ x := (hκ.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hdΦ : DifferentiableAt ℝ Φ (κ x) :=
    (hΦ.contDiffAt (hU.mem_nhds (hκO x hx).2.1)).differentiableAt (by simp)
  have h1 := hdΦ.hasFDerivAt.comp x hd.hasFDerivAt
  have hev : (Φ ∘ κ) =ᶠ[nhds x] id := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact (hκO y hy).2.2
  have h2 : HasFDerivAt (Φ ∘ κ) (ContinuousLinearMap.id ℝ (Fin d → ℝ)) x :=
    (hasFDerivAt_id x).congr_of_eventuallyEq hev
  have := h1.unique h2
  exact congrArg (fun L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) => L v) this

theorem vr_onto {d : ℕ} {O : Set (Fin d → ℝ)} {U : Set (B.Mat k r)} {κ : (Fin d → ℝ) → B.Mat k r}
    {Φ : B.Mat k r → (Fin d → ℝ)} (hC : IsChart k r d O U κ Φ) {x : Fin d → ℝ} (hx : x ∈ O) (v : Fin d → ℝ) :
    ∃ Y : B.Mat k r, B.inLie k r Y ∧ VR κ Φ Y x = v := by
  have hG : ∀ y ∈ O, κ y ∈ B.GV k r := fun y hy => (hC.2.2.2.2.1 y hy).1
  have hg : (κ x)ᴴ * Hpk k r * κ x = Hpk k r := hG x hx
  have hdet : IsUnit (κ x).det := Formalism.FourierDecayAlt.P.PBG.isUnit_det_of_UH (hG x hx)
  have hT := tangent_eq hC.1 hC.2.2.1 hG hx v
  set g := κ x with hgdef
  set A := fderiv ℝ κ x v with hAdef
  refine ⟨g⁻¹ * A, ?_, ?_⟩
  · have e1 : (g⁻¹)ᴴ * Hpk k r = Hpk k r * g := by
      calc (g⁻¹)ᴴ * Hpk k r = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) := by rw [hg]
        _ = (g * g⁻¹)ᴴ * Hpk k r * g := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = Hpk k r * g := by rw [Matrix.mul_nonsing_inv g hdet]; simp
    have e2 : Hpk k r * g⁻¹ = gᴴ * Hpk k r := by
      calc Hpk k r * g⁻¹ = gᴴ * Hpk k r * g * g⁻¹ := by rw [hg]
        _ = gᴴ * Hpk k r := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv g hdet, Matrix.mul_one]
    show (g⁻¹ * A)ᴴ * Hpk k r + Hpk k r * (g⁻¹ * A) = 0
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, e1, ← Matrix.mul_assoc (Hpk k r), e2, ← Matrix.mul_assoc]
    exact hT
  · show fderiv ℝ Φ g (g * (g⁻¹ * A)) = v
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv g hdet, Matrix.one_mul]
    exact chart_id hC hx v

def ellL {d : ℕ} (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (x ξ : Fin d → ℝ) :
    B.Mat k r →ₗ[ℝ] ℝ where
  toFun X := ξ ⬝ᵥ VR κ Φ X x
  map_add' X Y := by simp only [VR, Matrix.mul_add, map_add, dotProduct_add]
  map_smul' c X := by simp only [VR, Matrix.mul_smul, map_smul, dotProduct_smul, RingHom.id_apply, smul_eq_mul]

theorem ellL_apply {d : ℕ} (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (x ξ : Fin d → ℝ)
    (X : B.Mat k r) : ellL κ Φ x ξ X = ξ ⬝ᵥ VR κ Φ X x := rfl

def cMat (ℓ : B.Mat k r →ₗ[ℝ] ℝ) : B.Mat k r :=
  Matrix.of fun j i => ((ℓ (Matrix.single i j 1) : ℝ) : ℂ) - Complex.I * ((ℓ (Complex.I • Matrix.single i j 1) : ℝ) : ℂ)

theorem ell_single (ℓ : B.Mat k r →ₗ[ℝ] ℝ) (i j : Fin (2 * r + k + 1)) (c : ℂ) :
    ℓ (Matrix.single i j c) = c.re * ℓ (Matrix.single i j 1) + c.im * ℓ (Complex.I • Matrix.single i j 1) := by
  have : (Matrix.single i j c : B.Mat k r) =
      c.re • (Matrix.single i j (1 : ℂ) : B.Mat k r) + c.im • (Complex.I • (Matrix.single i j (1 : ℂ) : B.Mat k r)) := by
    ext p q
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply]
    split_ifs <;> simp
  rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

theorem re_trace_cMat (ℓ : B.Mat k r →ₗ[ℝ] ℝ) (X : B.Mat k r) : (Matrix.trace (cMat ℓ * X)).re = ℓ X := by
  conv_rhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, cMat, Matrix.of_apply, Complex.re_sum, Complex.mul_re,
    Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_im]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [ell_single ℓ i j (X i j)]
  norm_num
  ring

theorem inLie_half (C : B.Mat k r) : B.inLie k r ((1 / 2 : ℂ) • (C - Hpk k r * Cᴴ * Hpk k r)) := by
  have hH : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1
  have hH' : ∀ M : B.Mat k r, Hpk k r * (Hpk k r * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hH, Matrix.one_mul]
  have hHc : (Hpk k r)ᴴ = Hpk k r := (hpkFacts k r).1
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp
  show ((1 / 2 : ℂ) • (C - Hpk k r * Cᴴ * Hpk k r))ᴴ * Hpk k r +
    Hpk k r * ((1 / 2 : ℂ) • (C - Hpk k r * Cᴴ * Hpk k r)) = 0
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hHc,
    Matrix.conjTranspose_conjTranspose, hs]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hH, hH',
    Matrix.mul_one]
  rw [← smul_add]
  have : Cᴴ * Hpk k r - Hpk k r * C + (Hpk k r * C - Cᴴ * Hpk k r) = 0 := by abel
  rw [this, smul_zero]

theorem re_trace_half (C X : B.Mat k r) (hX : B.inLie k r X) :
    (Matrix.trace ((1 / 2 : ℂ) • (C - Hpk k r * Cᴴ * Hpk k r) * X)).re = (Matrix.trace (C * X)).re := by
  have hH : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1
  have hX' : Hpk k r * (X * Hpk k r) = -Xᴴ := by
    have h : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
    have h2 := congrArg (· * Hpk k r) h
    simp only [Matrix.add_mul, Matrix.mul_assoc, hH, Matrix.mul_one, Matrix.zero_mul] at h2
    exact eq_neg_of_add_eq_zero_right h2
  have e1 : Matrix.trace (Hpk k r * Cᴴ * Hpk k r * X) = -star (Matrix.trace (C * X)) := by
    calc Matrix.trace (Hpk k r * Cᴴ * Hpk k r * X) = Matrix.trace (Hpk k r * (Cᴴ * Hpk k r * X)) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Cᴴ * (Hpk k r * (X * Hpk k r))) := by
          rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
      _ = -Matrix.trace ((X * C)ᴴ) := by
          rw [hX', Matrix.mul_neg, Matrix.trace_neg, Matrix.conjTranspose_mul]
      _ = -star (Matrix.trace (C * X)) := by rw [Matrix.trace_conjTranspose, Matrix.trace_mul_comm]
  rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.sub_mul, Matrix.trace_sub, e1, smul_eq_mul]
  simp [Complex.mul_re]
  ring

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity.ChartCovPf

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

open ChartCovPf in

theorem chart_covariance_holds : ChartCov := by
  intro k r d O U κ Φ hC x hx ξ
  refine ⟨(1 / 2 : ℂ) • (cMat (ellL κ Φ x ξ) - Hpk k r * (cMat (ellL κ Φ x ξ))ᴴ * Hpk k r),
    inLie_half _, ?_, ?_⟩
  · intro hξ h0
    obtain ⟨Y, hY, hYv⟩ := vr_onto hC hx ξ
    have e := re_trace_half (cMat (ellL κ Φ x ξ)) Y hY
    rw [h0, Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re, re_trace_cMat, ellL_apply, hYv] at e
    exact hξ (dotProduct_self_eq_zero.1 e.symm)
  · intro X hX
    rw [re_trace_half _ X hX, re_trace_cMat, ellL_apply]

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
