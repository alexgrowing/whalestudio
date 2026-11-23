import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.MkLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SgLaws

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.I

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem matrix_two_by_two_congr {R : Type} {a b c d a' b' c' d' : R} (h1 : a = a') (h2 : b = b') (h3 : c = c')
    (h4 : d = d') : !![a, b; c, d] = !![a', b'; c', d'] := by
  rw [h1, h2, h3, h4]

private theorem gl_val (z : A E) : (gl (nU z)).val = !![1, z; 0, 1] := rfl

private theorem inv_nU (z : A E) : (gl (nU z))⁻¹ = gl (nU (-z)) := by
  refine inv_eq_of_mul_eq_one_right ?_
  apply Units.ext
  rw [Units.val_mul, gl_val, gl_val, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem act_entry (D : Dat F E) (z : A E) (X : V4 F) :
    (gl (nU (-z))).val * D.herm X * ((gl (nU (-z))).val.map D.bar)ᵀ =
      !![D.mkE (X 1) 0 - z * D.mkE (X 2) (-X 3) - (D.mkE (X 2) (X 3) - z * D.mkE (X 0) 0) * D.bar z,
         D.mkE (X 2) (X 3) - z * D.mkE (X 0) 0;
         D.mkE (X 2) (-X 3) - D.mkE (X 0) 0 * D.bar z, D.mkE (X 0) 0] := by
  rw [gl_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Dat.herm, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem weilAction_unipotent_null (D : Dat F E) (a b : A F) (hN : a ^ 2 - rt D.δ * b ^ 2 = 0) (X : V4 F) :
    D.act (gl (nU (-D.mkE a b))) X =
      ![X 0, X 1 - 2 * (a * X 2) + 2 * (rt D.δ * (b * X 3)), X 2 - a * X 0, X 3 - b * X 0] := by
  obtain ⟨hmul, hadd, -, hco, -, hbar, -⟩ := mkLaws F E D
  have hsub : ∀ u t u' t', D.mkE u t - D.mkE u' t' = D.mkE (u - u') (t - t') := by
    intro u t u' t'
    rw [sub_eq_iff_eq_add, hadd, sub_add_cancel, sub_add_cancel]
  have e00 : D.mkE (X 1) 0 - D.mkE a b * D.mkE (X 2) (-X 3) -
      (D.mkE (X 2) (X 3) - D.mkE a b * D.mkE (X 0) 0) * D.bar (D.mkE a b) =
      D.mkE (X 1 - 2 * (a * X 2) + 2 * (rt D.δ * (b * X 3))) 0 := by
    simp only [hbar, hmul, hsub]
    congr 1
    · linear_combination (X 0) * hN
    · ring
  have e01 : D.mkE (X 2) (X 3) - D.mkE a b * D.mkE (X 0) 0 = D.mkE (X 2 - a * X 0) (X 3 - b * X 0) := by
    simp only [hmul, hsub]
    congr 1 <;> ring
  rw [Dat.act, act_entry, e00, e01]
  ext1 i
  fin_cases i
  · change D.co (D.mkE (X 0) 0) 0 = X 0
    rw [hco]; rfl
  · change D.co (D.mkE (X 1 - 2 * (a * X 2) + 2 * (rt D.δ * (b * X 3))) 0) 0 = _
    rw [hco]; rfl
  · change D.co (D.mkE (X 2 - a * X 0) (X 3 - b * X 0)) 0 = _
    rw [hco]; rfl
  · change D.co (D.mkE (X 2 - a * X 0) (X 3 - b * X 0)) 1 = _
    rw [hco]; rfl

end UpperTheory.ConvolutionTheory.R2.I

theorem UpperTheory.ConvolutionTheory.R2.I.actN :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (v : P F) (θ : Kv v), θ ^ 2 = algebraMap F (Kv v) D.δ → θ ≠ 0 → ∀ s,
      nu F (nbar D v θ s) = 1 ∧
      ∀ X, away v (D.act (nbar D v θ s)⁻¹ X) = away v X ∧ mat v θ (D.act (nbar D v θ s)⁻¹ X) = mat v θ X * !![1, 0; -s, 1] := by
  intro F E _ _ _ _ _ D v θ hθ hθ0 s
  obtain ⟨sadd, smul, scp, -, -, -, -, -, -, -⟩ := sgLaws F v
  have h2 : (2 : Kv v) ≠ 0 := by norm_num
  have hδ : cp v (rt D.δ) = θ ^ 2 := hθ.symm ▸ rfl
  have s0 : sg v 0 = 0 := by
    have := sadd 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  have sneg : ∀ x, sg v (-x) = -sg v x := by
    intro x
    have := sadd x (-x)
    rw [add_neg_cancel, s0] at this
    exact eq_neg_of_add_eq_zero_right this.symm
  refine ⟨?_, fun X => ?_⟩
  · have : Matrix.GeneralLinearGroup.det (nbar D v θ s) = 1 := by
      apply Units.ext
      simp [nbar, Matrix.det_fin_two]
    rw [nu, this, map_one]
  set a := sg v (s / 2) with ha
  set b := sg v (-(s / (2 * θ))) with hb
  have hN : a ^ 2 - rt D.δ * b ^ 2 = 0 := by
    rw [pow_two, pow_two, ← mul_assoc]
    rw [ha, hb, smul, smul, smul, scp, scp, hδ, sub_eq_zero]
    congr 1
    field_simp
  let d : Fin 4 → Kv v := ![0, -(s * cp v (X 2)) - s * θ * cp v (X 3), -(s / 2 * cp v (X 0)), s / (2 * θ) * cp v (X 0)]
  have hX : D.act (nbar D v θ s)⁻¹ X = fun i => X i + sg v (d i) := by
    rw [nbar, inv_nU, weilAction_unipotent_null D a b hN X]
    ext1 i
    fin_cases i
    · simp [d, s0]
    · have e0 : d 1 = -(cp v (2 * X 2) * (s / 2)) + cp v (2 * (rt D.δ * X 3)) * (-(s / (2 * θ))) := by
        change -(s * cp v (X 2)) - s * θ * cp v (X 3) = _
        rw [map_mul, map_mul, map_mul, hδ, map_ofNat]
        field_simp
        ring
      have e1 : sg v (d 1) = -(2 * (a * X 2)) + 2 * (rt D.δ * (b * X 3)) := by
        rw [e0, sadd, sneg, ← smul, ← smul]
        ring
      change X 1 - 2 * (a * X 2) + 2 * (rt D.δ * (b * X 3)) = X 1 + sg v (d 1)
      rw [e1]
      ring
    · have e0 : d 2 = -(cp v (X 0) * (s / 2)) := by
        change -(s / 2 * cp v (X 0)) = _
        ring
      have e1 : sg v (d 2) = -(a * X 0) := by
        rw [e0, sneg, ← smul]
        ring
      change X 2 - a * X 0 = X 2 + sg v (d 2)
      rw [e1]
      ring
    · have e0 : d 3 = -(cp v (X 0) * (-(s / (2 * θ)))) := by
        change s / (2 * θ) * cp v (X 0) = _
        ring
      have e1 : sg v (d 3) = -(b * X 0) := by
        rw [e0, sneg, ← smul]
        ring
      change X 3 - b * X 0 = X 3 + sg v (d 3)
      rw [e1]
      ring
  have hcp : ∀ i, cp v (D.act (nbar D v θ s)⁻¹ X i) = cp v (X i) + d i := by
    intro i
    rw [hX]
    change cp v (X i + sg v (d i)) = _
    rw [map_add, scp]
  constructor
  · funext i
    change D.act (nbar D v θ s)⁻¹ X i - sg v (cp v (D.act (nbar D v θ s)⁻¹ X i)) = X i - sg v (cp v (X i))
    rw [hcp, sadd, hX]
    change X i + sg v (d i) - _ = _
    ring
  · simp only [mat, hcp]
    rw [Matrix.mul_fin_two]
    refine matrix_two_by_two_congr ?_ ?_ ?_ ?_
    · change cp v (X 1) + (-(s * cp v (X 2)) - s * θ * cp v (X 3)) = _
      ring
    · change cp v (X 2) + -(s / 2 * cp v (X 0)) + (cp v (X 3) + s / (2 * θ) * cp v (X 0)) * θ = _
      field_simp
      ring
    · change cp v (X 2) + -(s / 2 * cp v (X 0)) - (cp v (X 3) + s / (2 * θ) * cp v (X 0)) * θ = _
      field_simp
      ring
    · change cp v (X 0) + 0 = _
      ring
