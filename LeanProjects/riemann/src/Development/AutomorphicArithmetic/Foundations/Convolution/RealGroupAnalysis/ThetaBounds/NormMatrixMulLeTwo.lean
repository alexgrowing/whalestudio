import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem ht_le {E : Type} [Field E] [NumberField E] (y : GL (Fin 2) (Cinf E)) :
    ‖toL y.val‖ ≤ GlobalTheory.CuspRep.height y ∧ ‖toL (y⁻¹).val‖ ≤ GlobalTheory.CuspRep.height y := by
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  refine ⟨?_, ?_⟩ <;> first | (unfold GlobalTheory.CuspRep.height; linarith) | fail "height"

private theorem norm_matrix_mul_le_two {E : Type} [Field E] [NumberField E]
    (x x' : Matrix (Fin 2) (Fin 2) (Cinf E)) : ‖toL (x * x')‖ ≤ 2 * ‖toL x‖ * ‖toL x'‖ := by
  have h0 : 0 ≤ 2 * ‖toL x‖ * ‖toL x'‖ := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j =>
    (pi_norm_le_iff_of_nonneg h0).2 fun w => ?_
  have e1 : ∀ a b, ‖x a b w‖ ≤ ‖toL x‖ := fun a b =>
    (norm_le_pi_norm (x a b) w).trans ((norm_le_pi_norm (toL x a) b).trans (norm_le_pi_norm (toL x) a))
  have e2 : ∀ a b, ‖x' a b w‖ ≤ ‖toL x'‖ := fun a b =>
    (norm_le_pi_norm (x' a b) w).trans ((norm_le_pi_norm (toL x' a) b).trans (norm_le_pi_norm (toL x') a))
  have e : toL (x * x') i j w = x i 0 w * x' 0 j w + x i 1 w * x' 1 j w := by
    show (x * x') i j w = _
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [e]
  have p : ∀ k, ‖x i k w * x' k j w‖ ≤ ‖toL x‖ * ‖toL x'‖ := fun k => by
    rw [norm_mul]
    exact mul_le_mul (e1 _ _) (e2 _ _) (norm_nonneg _) (norm_nonneg _)
  have := norm_add_le (x i 0 w * x' 0 j w) (x i 1 w * x' 1 j w)
  linarith [p 0, p 1]

private theorem cont_toL {E : Type} [Field E] [NumberField E] :
    Continuous fun x : Matrix (Fin 2) (Fin 2) (Cinf E) => toL x :=
  continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem i j

theorem UpperTheory.ConvolutionTheory.R2.Ff.htLe :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], HtLe E := by
  intro E _ _ _
  refine ⟨?_, fun y => ⟨?_, ?_, fun y' => ?_⟩⟩
  · unfold Ht
    have c1 : Continuous fun y : GL (Fin 2) (Cinf E) => toL y.val := cont_toL.comp Units.continuous_val
    have c2 : Continuous fun y : GL (Fin 2) (Cinf E) => toL (y⁻¹).val :=
      cont_toL.comp (Units.continuous_val.comp continuous_inv)
    exact (continuous_const.add c1.norm).add c2.norm
  · have n1 := norm_nonneg (toL y.val)
    have n2 := norm_nonneg (toL (y⁻¹).val)
    unfold Ht
    linarith
  · have h := ht_le y
    have h1 := GlobalTheory.CuspRep.one_le_height y
    unfold Ht
    linarith [h.1, h.2]
  · have n1 := norm_nonneg (toL y.val)
    have n2 := norm_nonneg (toL (y⁻¹).val)
    have n3 := norm_nonneg (toL y'.val)
    have n4 := norm_nonneg (toL (y'⁻¹).val)
    have m1 := norm_matrix_mul_le_two y.val y'.val
    have m2 := norm_matrix_mul_le_two (y'⁻¹).val (y⁻¹).val
    have e1 : (y * y').val = y.val * y'.val := rfl
    have e2 : ((y * y')⁻¹).val = (y'⁻¹).val * (y⁻¹).val := by rw [_root_.mul_inv_rev]; rfl
    unfold Ht
    rw [e1, e2]
    nlinarith [mul_nonneg n1 n3, mul_nonneg n1 n4, mul_nonneg n2 n3, mul_nonneg n2 n4]
