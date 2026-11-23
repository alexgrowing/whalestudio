import Formalism.HermitianCurvature.HermitianCurvatureProofs.InnerBound

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem meas_G (γ : Mx k r) (b : ℝ) :
    Measurable (fun pp : B.SS k r =>
      ‖B.gN (Matrix.of pp.1.1 * Matrix.of pp.1.2 * γ * (Matrix.of pp.2.2)⁻¹ * (Matrix.of pp.2.1)⁻¹) ^ (-b)‖ₑ) := by
  have hi := B2x1.invM_meas (k := k) (r := r)
  have m1 : Measurable (fun pp : B.SS k r => pp.1.1) := measurable_fst.fst
  have m2 : Measurable (fun pp : B.SS k r => pp.1.2) := measurable_fst.snd
  have m3 : Measurable (fun pp : B.SS k r => B2.invM pp.2.2) := hi.comp measurable_snd.snd
  have m4 : Measurable (fun pp : B.SS k r => B2.invM pp.2.1) := hi.comp measurable_snd.fst
  have mγ : Measurable (fun _ : B.SS k r => (Matrix.of.symm γ : Formalism.QuantumDeterminants.Mt k r)) := measurable_const
  have M := meas_matmul (meas_matmul (meas_matmul (meas_matmul m1 m2) mγ) m3) m4
  have hg : Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => B.gN (Matrix.of y)) := gN_cont.comp mt_cont
  exact ((hg.measurable.comp M).pow_const (-b)).enorm

def Phi3 (e1 e2 : Mx k r → ℂ) (γi : Mx k r) (x : Formalism.QuantumDeterminants.Mt k r) (p q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) :
    ℝ≥0∞ :=
  ‖e1 (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)‖ₑ * ‖e2 (Matrix.of q.1 * Matrix.of q.2 * (γi * Matrix.of x))‖ₑ

theorem triple_integrand_measurable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {e1 e2 : Mx k r → ℂ} (he1 : Continuous e1) (he2 : Continuous e2) (γi : Mx k r)
    {X : α → Formalism.QuantumDeterminants.Mt k r} {Pp Qq : α → Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r}
    (hX : Continuous X) (hP : Continuous Pp) (hQ : Continuous Qq) :
    Measurable (fun t => Phi3 e1 e2 γi (X t) (Pp t) (Qq t)) := by
  unfold Phi3
  exact ((he1.comp (((mt_cont.comp hP.fst).matrix_mul (mt_cont.comp hP.snd)).matrix_mul
    (mt_cont.comp hX))).enorm.measurable).mul
    ((he2.comp (((mt_cont.comp hQ.fst).matrix_mul (mt_cont.comp hQ.snd)).matrix_mul
    (continuous_const.matrix_mul (mt_cont.comp hX)))).enorm.measurable)

theorem triple_lintegral_product {e1 e2 : Mx k r → ℂ} (he1 : Continuous e1) (he2 : Continuous e2) (γi : Mx k r)
    (μp μq : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (x : Formalism.QuantumDeterminants.Mt k r) :
    (∫⁻ p, ‖e1 (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)‖ₑ ∂μp) *
      (∫⁻ q, ‖e2 (Matrix.of q.1 * Matrix.of q.2 * (γi * Matrix.of x))‖ₑ ∂μq) =
      ∫⁻ p, ∫⁻ q, Phi3 e1 e2 γi x p q ∂μq ∂μp := by
  simp only [Phi3]
  have ha : Measurable fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      ‖e1 (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)‖ₑ :=
    (he1.comp (((mt_cont.comp continuous_fst).matrix_mul (mt_cont.comp continuous_snd)).matrix_mul
      continuous_const)).enorm.measurable
  rw [← lintegral_mul_const _ ha]
  refine lintegral_congr fun p => ?_
  rw [lintegral_const_mul' _ _ enorm_ne_top]

theorem triple_lintegral_swap {e1 e2 : Mx k r → ℂ} (he1 : Continuous e1) (he2 : Continuous e2) (γi : Mx k r)
    (μG : Measure (Formalism.QuantumDeterminants.Mt k r)) (μp μq : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r))
    [SFinite μG] [SFinite μp] [SFinite μq] :
    ∫⁻ x, ∫⁻ p, ∫⁻ q, Phi3 e1 e2 γi x p q ∂μq ∂μp ∂μG =
      ∫⁻ p, ∫⁻ q, ∫⁻ x, Phi3 e1 e2 γi x p q ∂μG ∂μq ∂μp := by
  have h1 : Measurable (Function.uncurry fun (x : Formalism.QuantumDeterminants.Mt k r)
      (p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => ∫⁻ q, Phi3 e1 e2 γi x p q ∂μq) := by
    have hm := triple_integrand_measurable he1 he2 γi
      (α := (Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r))
      (X := fun z => z.1.1) (Pp := fun z => z.1.2) (Qq := fun z => z.2)
      (continuous_fst.comp continuous_fst) (continuous_snd.comp continuous_fst) continuous_snd
    exact hm.lintegral_prod_right'
  rw [lintegral_lintegral_swap h1.aemeasurable]
  refine lintegral_congr fun p => ?_
  have h2 : Measurable (Function.uncurry fun (x : Formalism.QuantumDeterminants.Mt k r)
      (q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => Phi3 e1 e2 γi x p q) :=
    triple_integrand_measurable he1 he2 γi (X := fun z : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => z.1)
      (Pp := fun _ => p) (Qq := fun z => z.2) continuous_fst continuous_const continuous_snd
  exact lintegral_lintegral_swap h2.aemeasurable

end Formalism.FourierDecayAlt.P.S3dx4
