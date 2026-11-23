import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousSandwichedProduct

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

def abelian₂ (e0 : Mx k r → ℂ) (γ : Mx k r) (μp μq : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r))
    (x y : Formalism.QuantumDeterminants.Mt k r) : ℝ≥0∞ :=
  ∫⁻ p, ∫⁻ q, ‖e0 ((Matrix.of x)⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * γ * (Matrix.of q.1 * Matrix.of q.2)⁻¹ *
    Matrix.of y)‖ₑ ∂μq ∂μp

def Lam1 (e0 : Mx k r → ℂ) (μp : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (x y : Formalism.QuantumDeterminants.Mt k r) :
    ℝ≥0∞ :=
  ∫⁻ p, ‖e0 ((Matrix.of x)⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * Matrix.of y)‖ₑ ∂μp

theorem meas_inv {α : Type*} [MeasurableSpace α] {f : α → Formalism.QuantumDeterminants.Mt k r} (hf : Measurable f) :
    Measurable (fun t => (fun i j => ((Matrix.of (f t))⁻¹ : Mx k r) i j : Formalism.QuantumDeterminants.Mt k r)) :=
  (B2x1.invM_meas (k := k) (r := r)).comp hf

theorem measurable_enorm_composition {e0 : Mx k r → ℂ} (he0 : Continuous e0) {α : Type*} [MeasurableSpace α]
    {f : α → Formalism.QuantumDeterminants.Mt k r} (hf : Measurable f) : Measurable (fun t => ‖e0 (Matrix.of (f t))‖ₑ) :=
  ((he0.comp mt_cont).measurable.comp hf).enorm

theorem meas_hn {α : Type*} [MeasurableSpace α] {f : α → Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r}
    (hf : Measurable f) :
    Measurable (fun t => (fun i j => (Matrix.of (f t).1 * Matrix.of (f t).2) i j : Formalism.QuantumDeterminants.Mt k r)) :=
  meas_matmul hf.fst hf.snd

theorem meas_lam_int {e0 : Mx k r → ℂ} (he0 : Continuous e0) (γ : Mx k r) {α : Type*} [MeasurableSpace α]
    {X Y : α → Formalism.QuantumDeterminants.Mt k r} {P Q : α → Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r}
    (hX : Measurable X) (hY : Measurable Y) (hP : Measurable P) (hQ : Measurable Q) :
    Measurable (fun t => ‖e0 ((Matrix.of (X t))⁻¹ * (Matrix.of (P t).1 * Matrix.of (P t).2) * γ *
      (Matrix.of (Q t).1 * Matrix.of (Q t).2)⁻¹ * Matrix.of (Y t))‖ₑ) := by
  have mγ : Measurable (fun _ : α => (Matrix.of.symm γ : Formalism.QuantumDeterminants.Mt k r)) := measurable_const
  have M := meas_matmul (meas_matmul (meas_matmul (meas_matmul (meas_inv hX) (meas_hn hP)) mγ)
    (meas_inv (meas_hn hQ))) hY
  exact measurable_enorm_composition he0 M

theorem measurable_lambda_integrand {e0 : Mx k r → ℂ} (he0 : Continuous e0) {α : Type*} [MeasurableSpace α]
    {X Y : α → Formalism.QuantumDeterminants.Mt k r} {P : α → Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r}
    (hX : Measurable X) (hY : Measurable Y) (hP : Measurable P) :
    Measurable (fun t => ‖e0 ((Matrix.of (X t))⁻¹ * (Matrix.of (P t).1 * Matrix.of (P t).2) *
      Matrix.of (Y t))‖ₑ) := by
  have M := meas_matmul (meas_matmul (meas_inv hX) (meas_hn hP)) hY
  exact measurable_enorm_composition he0 M

theorem meas_lam {e0 : Mx k r → ℂ} (he0 : Continuous e0) (γ : Mx k r)
    (μp μq : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) [SFinite μp] [SFinite μq] :
    Measurable (fun t : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => abelian₂ e0 γ μp μq t.1 t.2) := by
  unfold abelian₂
  have m4 := meas_lam_int he0 γ (α := ((Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) × (Formalism.QuantumDeterminants.Mt k r ×
      Formalism.QuantumDeterminants.Mt k r)) × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r))
    (measurable_fst.fst.fst) (measurable_fst.fst.snd) measurable_fst.snd measurable_snd
  have m3 := m4.lintegral_prod_right' (ν := μq)
  exact m3.lintegral_prod_right' (ν := μp)

theorem measurable_lambda_integral {e0 : Mx k r → ℂ} (he0 : Continuous e0)
    (μp : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) [SFinite μp] :
    Measurable (fun t : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => Lam1 e0 μp t.1 t.2) := by
  unfold Lam1
  have m3 := measurable_lambda_integrand he0 (α := (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) × (Formalism.QuantumDeterminants.Mt k r ×
      Formalism.QuantumDeterminants.Mt k r)) (measurable_fst.fst) (measurable_fst.snd) measurable_snd
  exact m3.lintegral_prod_right' (ν := μp)

theorem meas_const_mt (c : Formalism.QuantumDeterminants.Mt k r) {α : Type*} [MeasurableSpace α] :
    Measurable (fun _ : α => c) := measurable_const

theorem lam_left {e0 : Mx k r → ℂ} (he0 : Continuous e0) (γ : Mx k r) {z : Fin (2 * r + k + 1) → ℂ}
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) [SigmaFinite μW] [SigmaFinite μN]
    (hz : Formalism.QuantumDeterminants.inWb k r z) (μq : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) [SFinite μq]
    {h0 n0 : Mx k r} (hh0 : h0 ∈ Formalism.QuantumDeterminants.UWset k r z) (hn0 : n0 ∈ Formalism.QuantumDeterminants.Nset k r) (x y : Formalism.QuantumDeterminants.Mt k r) :
    abelian₂ e0 γ (μW.prod μN) μq (fun i j => (h0 * n0 * Matrix.of x) i j) y = abelian₂ e0 γ (μW.prod μN) μq x y := by
  have hS : h0 * n0 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hh0.1 hn0.1
  obtain ⟨-, -, hSS⟩ := MatrixMultiplicationContinuity.uh_inv hS
  set x' : Formalism.QuantumDeterminants.Mt k r := fun i j => (h0 * n0 * Matrix.of x) i j with hx'
  set F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := fun m => ∫⁻ q, ‖e0 ((Matrix.of x')⁻¹ * Matrix.of m * γ *
    (Matrix.of q.1 * Matrix.of q.2)⁻¹ * Matrix.of y)‖ₑ ∂μq with hF
  have hFm : Measurable F := by
    have mγ : Measurable (fun _ : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
        (Matrix.of.symm γ : Formalism.QuantumDeterminants.Mt k r)) := measurable_const
    have M := meas_matmul (meas_matmul (meas_matmul (meas_matmul (meas_inv (meas_const_mt x'))
      measurable_fst) mγ) (meas_inv (meas_hn measurable_snd))) (meas_const_mt y)
    exact (measurable_enorm_composition he0 M).lintegral_prod_right'
  have hpl := param_left hW hN hz hh0 hn0 hFm
  unfold abelian₂
  calc ∫⁻ p, ∫⁻ q, ‖e0 ((Matrix.of x')⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * γ *
        (Matrix.of q.1 * Matrix.of q.2)⁻¹ * Matrix.of y)‖ₑ ∂μq ∂(μW.prod μN)
      = ∫⁻ p, F (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) ∂(μW.prod μN) := rfl
    _ = ∫⁻ p, F (fun i j => (h0 * n0 * (Matrix.of p.1 * Matrix.of p.2)) i j) ∂(μW.prod μN) := hpl.symm
    _ = _ := by
        have hmat : ∀ P : Mx k r, (Matrix.of x')⁻¹ * Matrix.of (fun i j => (h0 * n0 * P) i j : Formalism.QuantumDeterminants.Mt k r) =
            (Matrix.of x)⁻¹ * P := by
          intro P
          show (h0 * n0 * Matrix.of x)⁻¹ * (h0 * n0 * P) = (Matrix.of x)⁻¹ * P
          rw [Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc (h0 * n0)⁻¹, hSS, Matrix.one_mul]
        simp only [hF, hmat]

theorem lam_right {e0 : Mx k r → ℂ} (he0 : Continuous e0) (γ : Mx k r) {z : Fin (2 * r + k + 1) → ℂ}
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) [SigmaFinite μW] [SigmaFinite μN]
    (hz : Formalism.QuantumDeterminants.inWb k r z) (μp : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r))
    {h0 n0 : Mx k r} (hh0 : h0 ∈ Formalism.QuantumDeterminants.UWset k r z) (hn0 : n0 ∈ Formalism.QuantumDeterminants.Nset k r) (x y : Formalism.QuantumDeterminants.Mt k r) :
    abelian₂ e0 γ μp (μW.prod μN) x (fun i j => (h0 * n0 * Matrix.of y) i j) = abelian₂ e0 γ μp (μW.prod μN) x y := by
  have hS : h0 * n0 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hh0.1 hn0.1
  obtain ⟨-, hSS, -⟩ := MatrixMultiplicationContinuity.uh_inv hS
  unfold abelian₂
  apply lintegral_congr
  intro p
  set y' : Formalism.QuantumDeterminants.Mt k r := fun i j => (h0 * n0 * Matrix.of y) i j with hy'
  set F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := fun m => ‖e0 ((Matrix.of x)⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * γ *
    (Matrix.of m)⁻¹ * Matrix.of y')‖ₑ with hF
  have hFm : Measurable F := by
    have mc : Measurable (fun _ : Formalism.QuantumDeterminants.Mt k r =>
        (fun i j => ((Matrix.of x)⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * γ) i j : Formalism.QuantumDeterminants.Mt k r)) :=
      measurable_const
    have M := meas_matmul (meas_matmul mc (meas_inv measurable_id)) (meas_const_mt y')
    exact measurable_enorm_composition he0 M
  have hpl := param_left hW hN hz hh0 hn0 hFm
  calc ∫⁻ q, ‖e0 ((Matrix.of x)⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * γ *
        (Matrix.of q.1 * Matrix.of q.2)⁻¹ * Matrix.of y')‖ₑ ∂(μW.prod μN)
      = ∫⁻ q, F (fun i j => (Matrix.of q.1 * Matrix.of q.2) i j) ∂(μW.prod μN) := rfl
    _ = ∫⁻ q, F (fun i j => (h0 * n0 * (Matrix.of q.1 * Matrix.of q.2)) i j) ∂(μW.prod μN) := hpl.symm
    _ = _ := by
        have hSS' := (MatrixMultiplicationContinuity.uh_inv hS).2.2
        have hmat : ∀ (Z Q : Mx k r), Z * (Matrix.of (fun i j => (h0 * n0 * Q) i j : Formalism.QuantumDeterminants.Mt k r))⁻¹ *
            Matrix.of y' = Z * Q⁻¹ * Matrix.of y := by
          intro Z Q
          show Z * (h0 * n0 * Q)⁻¹ * (h0 * n0 * Matrix.of y) = Z * Q⁻¹ * Matrix.of y
          rw [Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (h0 * n0)⁻¹, hSS',
            Matrix.one_mul, ← Matrix.mul_assoc]
        simp only [hF, hmat]

theorem lambda_left_translation {e0 : Mx k r → ℂ} (he0 : Continuous e0) {z : Fin (2 * r + k + 1) → ℂ}
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) [SigmaFinite μW] [SigmaFinite μN]
    (hz : Formalism.QuantumDeterminants.inWb k r z)
    {h0 n0 : Mx k r} (hh0 : h0 ∈ Formalism.QuantumDeterminants.UWset k r z) (hn0 : n0 ∈ Formalism.QuantumDeterminants.Nset k r) (x y : Formalism.QuantumDeterminants.Mt k r) :
    Lam1 e0 (μW.prod μN) (fun i j => (h0 * n0 * Matrix.of x) i j) y = Lam1 e0 (μW.prod μN) x y := by
  have hS : h0 * n0 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hh0.1 hn0.1
  obtain ⟨-, -, hSS⟩ := MatrixMultiplicationContinuity.uh_inv hS
  set x' : Formalism.QuantumDeterminants.Mt k r := fun i j => (h0 * n0 * Matrix.of x) i j with hx'
  set F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := fun m => ‖e0 ((Matrix.of x')⁻¹ * Matrix.of m * Matrix.of y)‖ₑ with hF
  have hFm : Measurable F :=
    measurable_enorm_composition he0 (meas_matmul (meas_matmul (meas_inv (meas_const_mt x')) measurable_id) (meas_const_mt y))
  have hpl := param_left hW hN hz hh0 hn0 hFm
  unfold Lam1
  calc ∫⁻ p, ‖e0 ((Matrix.of x')⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * Matrix.of y)‖ₑ ∂(μW.prod μN)
      = ∫⁻ p, F (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) ∂(μW.prod μN) := rfl
    _ = ∫⁻ p, F (fun i j => (h0 * n0 * (Matrix.of p.1 * Matrix.of p.2)) i j) ∂(μW.prod μN) := hpl.symm
    _ = _ := by
        have hmat : ∀ P : Mx k r, (Matrix.of x')⁻¹ * Matrix.of (fun i j => (h0 * n0 * P) i j : Formalism.QuantumDeterminants.Mt k r) =
            (Matrix.of x)⁻¹ * P := by
          intro P
          show (h0 * n0 * Matrix.of x)⁻¹ * (h0 * n0 * P) = (Matrix.of x)⁻¹ * P
          rw [Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc (h0 * n0)⁻¹, hSS, Matrix.one_mul]
        simp only [hF, hmat]

theorem lambda_right_translation {e0 : Mx k r → ℂ} (he0 : Continuous e0) {z : Fin (2 * r + k + 1) → ℂ}
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} (hW : B.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : B.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) [SigmaFinite μW] [SigmaFinite μN]
    (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z)
    {h0 n0 : Mx k r} (hh0 : h0 ∈ Formalism.QuantumDeterminants.UWset k r z) (hn0 : n0 ∈ Formalism.QuantumDeterminants.Nset k r) (x y : Formalism.QuantumDeterminants.Mt k r) :
    Lam1 e0 (μW.prod μN) x (fun i j => (h0 * n0 * Matrix.of y) i j) = Lam1 e0 (μW.prod μN) x y := by
  set F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := fun m => ‖e0 ((Matrix.of x)⁻¹ * Matrix.of m * Matrix.of y)‖ₑ with hF
  have hFm : Measurable F :=
    measurable_enorm_composition he0 (meas_matmul (meas_matmul (meas_inv (meas_const_mt x)) measurable_id) (meas_const_mt y))
  have hpr := param_right hW hN hz hT hh0 hn0 hFm
  unfold Lam1
  calc ∫⁻ p, ‖e0 ((Matrix.of x)⁻¹ * (Matrix.of p.1 * Matrix.of p.2) *
        Matrix.of (fun i j => (h0 * n0 * Matrix.of y) i j : Formalism.QuantumDeterminants.Mt k r))‖ₑ ∂(μW.prod μN)
      = ∫⁻ p, F (fun i j => (Matrix.of p.1 * Matrix.of p.2 * (h0 * n0)) i j) ∂(μW.prod μN) := by
        have hmat : ∀ P : Mx k r, (Matrix.of x)⁻¹ * P *
            Matrix.of (fun i j => (h0 * n0 * Matrix.of y) i j : Formalism.QuantumDeterminants.Mt k r) =
            (Matrix.of x)⁻¹ * Matrix.of (fun i j => (P * (h0 * n0)) i j : Formalism.QuantumDeterminants.Mt k r) * Matrix.of y := by
          intro P
          show (Matrix.of x)⁻¹ * P * (h0 * n0 * Matrix.of y) = (Matrix.of x)⁻¹ * (P * (h0 * n0)) * Matrix.of y
          simp only [Matrix.mul_assoc]
        simp only [hF, hmat]
    _ = ∫⁻ p, F (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) ∂(μW.prod μN) := hpr
    _ = _ := rfl

end Formalism.FourierDecayAlt.P.S3dx4
