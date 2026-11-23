import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.OneOf

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem infGL_scalarE {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (u : (Cinf E)ˣ) :
    infGL E 2 (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (infId E u) := by
  have h1 : pInf E (infId E u).val = u.val := by
    change pInf E (1 - sInf E 1 + sInf E _) = _
    have h : ∀ x, pInf E (sInf E x) = x := fun x => (infEq E).symm_apply_apply x
    simp [h]
  have h2 : pFin E (infId E u).val = 1 := by
    change (1 : Af E) - 0 + 0 = 1
    simp
  refine ga_ext ?_ ?_
  · rw [pInf_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h1]
  · rw [pFin_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h2]

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E]

private theorem det_mul_inv (y : GL (Fin 2) (Cinf E)) (w : InfinitePlace E) :
    y.val.det w * (y⁻¹).val.det w = 1 := by
  have h : y.val.det * (y⁻¹).val.det = 1 := by
    rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  exact congrFun h w

private theorem det_ne (y : GL (Fin 2) (Cinf E)) (w : InfinitePlace E) : y.val.det w ≠ 0 := fun h => by
  have := det_mul_inv y w
  rw [h, zero_mul] at this
  exact zero_ne_one this

private noncomputable def nd (y : GL (Fin 2) (Cinf E)) (w : InfinitePlace E) : ℝ := Real.sqrt ‖y.val.det w‖

private theorem nd_pos (y : GL (Fin 2) (Cinf E)) (w : InfinitePlace E) : 0 < nd y w :=
  Real.sqrt_pos.2 (norm_pos_iff.2 (det_ne y w))

private theorem nd_sq (y : GL (Fin 2) (Cinf E)) (w : InfinitePlace E) : nd y w ^ 2 = ‖y.val.det w‖ :=
  Real.sq_sqrt (norm_nonneg _)

private theorem nd_inv (y : GL (Fin 2) (Cinf E)) (w : InfinitePlace E) : (nd y w)⁻¹ = nd y⁻¹ w := by
  have h : ‖y.val.det w‖ * ‖(y⁻¹).val.det w‖ = 1 := by
    rw [← norm_mul, det_mul_inv, norm_one]
  have h' : nd y w * nd y⁻¹ w = 1 := by
    rw [nd, nd, ← Real.sqrt_mul (norm_nonneg _), h, Real.sqrt_one]
  exact (eq_inv_of_mul_eq_one_right h').symm

private theorem entry_le (x : Matrix (Fin 2) (Fin 2) (Cinf E)) (i j : Fin 2) (w : InfinitePlace E) :
    ‖x i j w‖ ≤ ‖toL x‖ :=
  (norm_le_pi_norm (x i j) w).trans ((norm_le_pi_norm (toL x i) j).trans (norm_le_pi_norm (toL x) i))

private theorem det_le (x : Matrix (Fin 2) (Fin 2) (Cinf E)) (w : InfinitePlace E) :
    ‖x.det w‖ ≤ 2 * ‖toL x‖ ^ 2 := by
  have e := entry_le x
  have n0 : 0 ≤ ‖toL x‖ := norm_nonneg _
  rw [Matrix.det_fin_two, Pi.sub_apply, Pi.mul_apply, Pi.mul_apply]
  calc _ ≤ ‖x 0 0 w * x 1 1 w‖ + ‖x 0 1 w * x 1 0 w‖ := norm_sub_le _ _
    _ = ‖x 0 0 w‖ * ‖x 1 1 w‖ + ‖x 0 1 w‖ * ‖x 1 0 w‖ := by rw [norm_mul, norm_mul]
    _ ≤ ‖toL x‖ * ‖toL x‖ + ‖toL x‖ * ‖toL x‖ := by
      gcongr <;> apply e
    _ = _ := by ring

private theorem nd_le (y : GL (Fin 2) (Cinf E)) (w : InfinitePlace E) :
    nd y w ≤ 2 * ‖toL y.val‖ := by
  have n0 : 0 ≤ ‖toL y.val‖ := norm_nonneg _
  refine Real.sqrt_le_iff.2 ⟨by positivity, (det_le y.val w).trans ?_⟩
  nlinarith [sq_nonneg ‖toL y.val‖]

private noncomputable def sg (y : GL (Fin 2) (Cinf E)) : (Cinf E)ˣ where
  val := fun w => ((nd y w : ℝ) : ℂ)
  inv := fun w => (((nd y w)⁻¹ : ℝ) : ℂ)
  val_inv := by
    funext w
    change ((nd y w : ℝ) : ℂ) * (((nd y w)⁻¹ : ℝ) : ℂ) = 1
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (nd_pos y w).ne', Complex.ofReal_one]
  inv_val := by
    funext w
    change (((nd y w)⁻¹ : ℝ) : ℂ) * ((nd y w : ℝ) : ℂ) = 1
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (nd_pos y w).ne', Complex.ofReal_one]

private theorem continuous_nd (w : InfinitePlace E) : Continuous fun y : GL (Fin 2) (Cinf E) => nd y w :=
  Real.continuous_sqrt.comp (continuous_norm.comp
    ((continuous_apply w).comp (Continuous.matrix_det Units.continuous_val)))

private theorem continuous_sg : Continuous (sg (E := E)) := by
  refine Units.continuous_iff.2 ⟨continuous_pi fun w => ?_, continuous_pi fun w => ?_⟩
  · exact Complex.continuous_ofReal.comp (continuous_nd w)
  · exact Complex.continuous_ofReal.comp ((continuous_nd w).inv₀ fun y => (nd_pos y w).ne')

private theorem sg_le (y : GL (Fin 2) (Cinf E)) : ‖(sg y).val‖ ≤ 2 * ‖toL y.val‖ :=
  (pi_norm_le_iff_of_nonneg (by positivity)).2 fun w => by
    change ‖((nd y w : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_of_nonneg (nd_pos y w).le]
    exact nd_le y w

private theorem sg_inv_le (y : GL (Fin 2) (Cinf E)) : ‖(sg y)⁻¹.val‖ ≤ 2 * ‖toL (y⁻¹).val‖ :=
  (pi_norm_le_iff_of_nonneg (by positivity)).2 fun w => by
    change ‖(((nd y w)⁻¹ : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real, nd_inv, Real.norm_of_nonneg (nd_pos y⁻¹ w).le]
    exact nd_le y⁻¹ w

private theorem sc_entry (s : (Cinf E)ˣ) (y : GL (Fin 2) (Cinf E)) (i j : Fin 2) :
    (Matrix.GeneralLinearGroup.scalar (Fin 2) s * y).val i j = s.val * y.val i j := by
  rw [Units.val_mul]
  change ((Matrix.diagonal (fun _ => s.val) : Matrix (Fin 2) (Fin 2) (Cinf E)) * y.val) i j = _
  rw [Matrix.diagonal_mul]

private theorem sc_le (s : (Cinf E)ˣ) (y : GL (Fin 2) (Cinf E)) :
    ‖toL (Matrix.GeneralLinearGroup.scalar (Fin 2) s * y).val‖ ≤ ‖s.val‖ * ‖toL y.val‖ :=
  (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => by
    change ‖(Matrix.GeneralLinearGroup.scalar (Fin 2) s * y).val i j‖ ≤ _
    rw [sc_entry]
    refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    exact (norm_le_pi_norm (toL y.val i) j).trans (norm_le_pi_norm (toL y.val) i)

private theorem tau_det (y : GL (Fin 2) (Cinf E)) (w : InfinitePlace E) :
    ‖(Matrix.GeneralLinearGroup.scalar (Fin 2) (sg y)⁻¹ * y).val.det w‖ = 1 := by
  have h : (Matrix.GeneralLinearGroup.scalar (Fin 2) (sg y)⁻¹).val.det w = (((nd y w)⁻¹ : ℝ) : ℂ) ^ 2 := by
    change (Matrix.diagonal fun _ => (sg y)⁻¹.val).det w = _
    rw [Matrix.det_diagonal, Fin.prod_univ_two, Pi.mul_apply, sq]
    rfl
  rw [Units.val_mul, Matrix.det_mul, Pi.mul_apply, h, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.2 (nd_pos y w).le), ← nd_sq, inv_pow,
    inv_mul_cancel₀ (pow_pos (nd_pos y w) 2).ne']

private theorem continuous_sc :
    Continuous (Matrix.GeneralLinearGroup.scalar (Fin 2) : (Cinf E)ˣ → GL (Fin 2) (Cinf E)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Continuous.matrix_diagonal (continuous_pi fun _ => Units.continuous_val)
  · have e : (fun x : (Cinf E)ˣ => (((Matrix.GeneralLinearGroup.scalar (Fin 2) x)⁻¹ : GL (Fin 2) (Cinf E)) :
        Matrix (Fin 2) (Fin 2) (Cinf E))) = fun x => Matrix.diagonal fun _ => (x⁻¹).val := by
      funext x
      rw [← map_inv]
      rfl
    rw [e]
    exact Continuous.matrix_diagonal (continuous_pi fun _ => Units.continuous_val.comp continuous_inv)

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.R2.Ff.dec :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (_D : Dat F E), Dec F E := by
  intro F E _ _ _ _ _ _ _ D
  refine ⟨sg, fun y => Matrix.GeneralLinearGroup.scalar (Fin 2) (sg y)⁻¹ * y, continuous_sg,
    (continuous_sc.comp continuous_sg.inv).mul continuous_id, fun y => ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [← infGL_scalarE, ← map_mul, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  · exact UpperTheory.ConvolutionTheory.R2.Ff.oneOf F E D _ fun w => tau_det y w
  · have hA := (sc_le (sg y)⁻¹ y).trans (mul_le_mul_of_nonneg_right (sg_inv_le y) (norm_nonneg _))
    have hB : ‖toL ((Matrix.GeneralLinearGroup.scalar (Fin 2) (sg y)⁻¹ * y)⁻¹).val‖ ≤
        2 * ‖toL y.val‖ * ‖toL (y⁻¹).val‖ := by
      have e : (Matrix.GeneralLinearGroup.scalar (Fin 2) (sg y)⁻¹ * y)⁻¹ =
          Matrix.GeneralLinearGroup.scalar (Fin 2) (sg y) * y⁻¹ := by
        rw [_root_.mul_inv_rev, ← map_inv, inv_inv]
        exact (Matrix.GeneralLinearGroup.scalar_commute _ _).symm
      rw [e]
      exact (sc_le (sg y) y⁻¹).trans (mul_le_mul_of_nonneg_right (sg_le y) (norm_nonneg _))
    have a0 : 0 ≤ ‖toL y.val‖ := norm_nonneg _
    have b0 : 0 ≤ ‖toL (y⁻¹).val‖ := norm_nonneg _
    unfold Ht
    nlinarith [mul_nonneg a0 b0, sq_nonneg ‖toL y.val‖, sq_nonneg ‖toL (y⁻¹).val‖]
  · have hs := sg_le y
    have hi := sg_inv_le y
    unfold Ht
    linarith
