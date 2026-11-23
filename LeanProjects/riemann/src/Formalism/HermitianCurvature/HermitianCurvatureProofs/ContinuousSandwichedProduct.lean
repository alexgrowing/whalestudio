import Formalism.HermitianCurvature.HermitianCurvatureProofs.GNSandwich
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

private theorem lintegral_comp_eq_of_map_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → α}
    (hμ : μ.map f = μ) {G : α → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G (f x) ∂μ = ∫⁻ x, G x ∂μ := by
  by_cases hf : AEMeasurable f μ
  · conv_rhs => rw [← hμ]
    rw [lintegral_map' hG.aemeasurable hf]
  · have h0 : μ = 0 := by
      rw [← hμ]
      exact Measure.map_of_not_aemeasurable hf
    simp [h0]

theorem lint_lmul {μ : Measure (Formalism.QuantumDeterminants.Mt k r)} {a : Mx k r} (hμ : μ.map (Formalism.QuantumDeterminants.lmulM a) = μ)
    {G : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G (Formalism.QuantumDeterminants.lmulM a x) ∂μ = ∫⁻ x, G x ∂μ := by
  exact lintegral_comp_eq_of_map_eq hμ hG

theorem param_left {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    [SigmaFinite μW] [SigmaFinite μN] (hz : Formalism.QuantumDeterminants.inWb k r z)
    {h0 n0 : Mx k r} (hh0 : h0 ∈ Formalism.QuantumDeterminants.UWset k r z) (hn0 : n0 ∈ Formalism.QuantumDeterminants.Nset k r)
    {F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F (fun i j => (h0 * n0 * (Matrix.of p.1 * Matrix.of p.2)) i j) ∂(μW.prod μN) =
      ∫⁻ p, F (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) ∂(μW.prod μN) := by
  have hm1 : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      F (fun i j => (h0 * n0 * (Matrix.of p.1 * Matrix.of p.2)) i j)) :=
    (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (h0 * n0 * (Matrix.of p.1 * Matrix.of p.2)) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
  have hm2 : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      F (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j)) :=
    (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
  have hm3 : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      F (fun i j => (h0 * Matrix.of p.1 * Matrix.of p.2) i j)) :=
    (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (h0 * Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
  have hae : ∀ᵐ x ∂μW, Matrix.of x ∈ Formalism.QuantumDeterminants.UWset k r z := ae_iff.mpr hW.2.2.1

  have step1 : (fun x => ∫⁻ y, F (fun i j => (h0 * n0 * (Matrix.of x * Matrix.of y)) i j) ∂μN) =ᵐ[μW]
      fun x => ∫⁻ y, F (fun i j => (h0 * Matrix.of x * Matrix.of y) i j) ∂μN := by
    filter_upwards [hae] with x hx
    obtain ⟨hxi, hx1, -⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hx
    have hm : (Matrix.of x)⁻¹ * n0 * Matrix.of x ∈ Formalism.QuantumDeterminants.Nset k r := by
      have h1 := (Formalism.QuantumDeterminants.uWNormal k r z hz _ hxi n0 hn0).1
      rwa [Matrix.nonsing_inv_nonsing_inv _ (Matrix.isUnit_det_of_right_inverse hx1)] at h1
    have hG : Measurable (fun w : Formalism.QuantumDeterminants.Mt k r =>
        F (fun i j => (h0 * Matrix.of x * Matrix.of w) i j)) :=
      (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun w : Formalism.QuantumDeterminants.Mt k r => (fun i j => (h0 * Matrix.of x * Matrix.of w) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
    have e1 : ∀ y : Formalism.QuantumDeterminants.Mt k r, h0 * n0 * (Matrix.of x * Matrix.of y) =
        h0 * Matrix.of x * Matrix.of (Formalism.QuantumDeterminants.lmulM ((Matrix.of x)⁻¹ * n0 * Matrix.of x) y) := by
      intro y
      show _ = h0 * Matrix.of x * ((Matrix.of x)⁻¹ * n0 * Matrix.of x * Matrix.of y)
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (Matrix.of x) (Matrix.of x)⁻¹, hx1, Matrix.one_mul]
    simp_rw [e1]
    exact lint_lmul (hN.2.2.2 _ hm) hG
  rw [MeasureTheory.lintegral_prod _ hm1.aemeasurable, MeasureTheory.lintegral_prod _ hm2.aemeasurable,
    MeasureTheory.lintegral_congr_ae step1,
    MeasureTheory.lintegral_lintegral_swap (f := fun (x y : Formalism.QuantumDeterminants.Mt k r) => F (fun i j => (h0 * Matrix.of x * Matrix.of y) i j))
      hm3.aemeasurable,
    MeasureTheory.lintegral_lintegral_swap (f := fun (x y : Formalism.QuantumDeterminants.Mt k r) => F (fun i j => (Matrix.of x * Matrix.of y) i j))
      hm2.aemeasurable]

  refine MeasureTheory.lintegral_congr fun y => ?_
  have hG : Measurable (fun w : Formalism.QuantumDeterminants.Mt k r => F (fun i j => (Matrix.of w * Matrix.of y) i j)) :=
    (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun w : Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of w * Matrix.of y) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
  have e2 : ∀ x : Formalism.QuantumDeterminants.Mt k r, h0 * Matrix.of x * Matrix.of y =
      Matrix.of (Formalism.QuantumDeterminants.lmulM h0 x) * Matrix.of y := fun x => rfl
  simp_rw [e2]
  exact lint_lmul (hW.2.2.2 h0 hh0) hG

theorem lint_rmul {μ : Measure (Formalism.QuantumDeterminants.Mt k r)} {a : Mx k r} (hμ : μ.map (B.rmulF a) = μ)
    {G : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G (B.rmulF a x) ∂μ = ∫⁻ x, G x ∂μ := by
  exact lintegral_comp_eq_of_map_eq hμ hG

theorem lint_conj {μ : Measure (Formalism.QuantumDeterminants.Mt k r)} {a : Mx k r} (hμ : μ.map (Formalism.QuantumDeterminants.conjM a) = μ)
    {G : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G (Formalism.QuantumDeterminants.conjM a x) ∂μ = ∫⁻ x, G x ∂μ := by
  exact lintegral_comp_eq_of_map_eq hμ hG

theorem param_right {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : B.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW) (hN : B.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    [SigmaFinite μW] [SigmaFinite μN] (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z)
    {h0 n0 : Mx k r} (hh0 : h0 ∈ Formalism.QuantumDeterminants.UWset k r z) (hn0 : n0 ∈ Formalism.QuantumDeterminants.Nset k r)
    {F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F (fun i j => (Matrix.of p.1 * Matrix.of p.2 * (h0 * n0)) i j) ∂(μW.prod μN) =
      ∫⁻ p, F (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) ∂(μW.prod μN) := by
  obtain ⟨hi, h1, -⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hh0
  have hinv : h0⁻¹⁻¹ = h0 := Matrix.nonsing_inv_nonsing_inv _ (Matrix.isUnit_det_of_right_inverse h1)
  have hconj : μN.map (Formalism.QuantumDeterminants.conjM h0⁻¹) = μN :=
    Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof k r z μN hz hT hN _ hi
  have hm1 : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      F (fun i j => (Matrix.of p.1 * Matrix.of p.2 * (h0 * n0)) i j)) :=
    (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of p.1 * Matrix.of p.2 * (h0 * n0)) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
  have hm2 : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      F (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j)) :=
    (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
  have hm3 : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      F (fun i j => (Matrix.of p.1 * h0 * Matrix.of p.2) i j)) :=
    (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of p.1 * h0 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)

  have inner : ∀ x : Formalism.QuantumDeterminants.Mt k r,
      ∫⁻ y, F (fun i j => (Matrix.of x * Matrix.of y * (h0 * n0)) i j) ∂μN =
        ∫⁻ y, F (fun i j => (Matrix.of x * h0 * Matrix.of y) i j) ∂μN := by
    intro x
    have hG1 : Measurable (fun w : Formalism.QuantumDeterminants.Mt k r =>
        F (fun i j => (Matrix.of x * h0 * Matrix.of w * n0) i j)) :=
      (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun w : Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of x * h0 * Matrix.of w * n0) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
    have hG2 : Measurable (fun w : Formalism.QuantumDeterminants.Mt k r =>
        F (fun i j => (Matrix.of x * h0 * Matrix.of w) i j)) :=
      (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun w : Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of x * h0 * Matrix.of w) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
    have e1 : ∀ y : Formalism.QuantumDeterminants.Mt k r, Matrix.of x * Matrix.of y * (h0 * n0) =
        Matrix.of x * h0 * Matrix.of (Formalism.QuantumDeterminants.conjM h0⁻¹ y) * n0 := by
      intro y
      show _ = Matrix.of x * h0 * (h0⁻¹ * Matrix.of y * h0⁻¹⁻¹) * n0
      rw [hinv]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc h0 h0⁻¹, h1, Matrix.one_mul]
    have e2 : ∀ y : Formalism.QuantumDeterminants.Mt k r, Matrix.of x * h0 * Matrix.of y * n0 =
        Matrix.of x * h0 * Matrix.of (B.rmulF n0 y) := by
      intro y
      show _ = Matrix.of x * h0 * (Matrix.of y * n0)
      simp only [Matrix.mul_assoc]
    simp_rw [e1]
    rw [lint_conj hconj hG1]
    simp_rw [e2]
    exact lint_rmul (hN.right n0 hn0) hG2
  rw [MeasureTheory.lintegral_prod _ hm1.aemeasurable, MeasureTheory.lintegral_prod _ hm2.aemeasurable]
  simp_rw [inner]
  rw [MeasureTheory.lintegral_lintegral_swap (f := fun (x y : Formalism.QuantumDeterminants.Mt k r) => F (fun i j => (Matrix.of x * h0 * Matrix.of y) i j))
      hm3.aemeasurable,
    MeasureTheory.lintegral_lintegral_swap (f := fun (x y : Formalism.QuantumDeterminants.Mt k r) => F (fun i j => (Matrix.of x * Matrix.of y) i j))
      hm2.aemeasurable]

  refine MeasureTheory.lintegral_congr fun y => ?_
  have hG3 : Measurable (fun w : Formalism.QuantumDeterminants.Mt k r => F (fun i j => (Matrix.of w * Matrix.of y) i j)) :=
    (hF.comp (by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [Matrix.mul_apply, Matrix.of_apply]
        fun_prop : Continuous (fun w : Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of w * Matrix.of y) i j : Formalism.QuantumDeterminants.Mt k r))).measurable)
  have e3 : ∀ x : Formalism.QuantumDeterminants.Mt k r, Matrix.of x * h0 * Matrix.of y =
      Matrix.of (B.rmulF h0 x) * Matrix.of y := fun x => rfl
  simp_rw [e3]
  exact lint_rmul (hW.right h0 hh0) hG3

end Formalism.FourierDecayAlt.P.S3dx4
