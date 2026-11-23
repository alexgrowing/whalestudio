import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ProjLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CutLim

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.flip :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (X : H →L[ℂ] H) (a b : ℝ), (∀ t h, X (M.F.U t h) = M.F.U (-t) (X h)) →
      IsHilbertSchmidt (M.P (Ioc a b) ∘L X) → IsHilbertSchmidt (X ∘L M.P (Ioc a b)) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M X a b hX hs
  obtain ⟨-, -, -, -, pl, p0, -, -⟩ := projLaws M
  rcases le_or_gt b a with hab | hab
  · rw [Ioc_eq_empty_of_le hab, p0, ContinuousLinearMap.comp_zero]
    show hsNormSq _ < _
    rw [hsNormSq_zero]; exact ENNReal.zero_lt_top
  set d := b - a with hd
  have d0 : 0 < d := sub_pos.2 hab
  let I : ℤ → Set ℝ := fun n => Ioc (a + n * d) (a + (n + 1) * d)
  have hI : ∀ n, MeasurableSet (I n) := fun _ => measurableSet_Ioc
  have sa : ∀ s, MeasurableSet s → ContinuousLinearMap.adjoint (M.P s) = M.P s := fun s hs => (pl s s hs hs).2.1.adjoint_eq
  have pyth : ∀ x : H, ‖x‖ₑ ^ 2 = ∑' n, ‖M.P (I n) x‖ₑ ^ 2 := fun x => by
    have h1 : HasSum (fun n => M.P (I n) x) x := by
      have h0 : HasSum (fun n => M.P (I n) x) (M.J (M.J.symm x)) :=
        ((cutLim (M.J.symm x)).2 a d d0).mapL (M.J.toContinuousLinearEquiv : L V →L[ℂ] H)
      rwa [M.J.apply_symm_apply] at h0
    have h2 := (h1.mapL (innerSL ℂ x)).mapL Complex.reCLM
    have e : ∀ n, (⟪x, M.P (I n) x⟫_ℂ).re = ‖M.P (I n) x‖ ^ 2 := fun n => by
      have i1 := DFunLike.congr_fun (pl _ _ (hI n) (hI n)).1 x
      rw [inter_self, ContinuousLinearMap.comp_apply] at i1
      rw [← i1, ← ContinuousLinearMap.adjoint_inner_left, sa _ (hI n), i1, inner_self_eq_norm_sq_to_K]
      simp [← Complex.ofReal_pow]
    simp only [innerSL_apply_apply, Complex.reCLM_apply, e] at h2
    rw [inner_self_eq_norm_sq_to_K] at h2
    have h3 : HasSum (fun n => ‖M.P (I n) x‖ ^ 2) (‖x‖ ^ 2) := by simpa [← Complex.ofReal_pow] using h2
    have h4 := ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg ‖M.P (I n) x‖) h3.summable
    rw [h3.tsum_eq] at h4
    simpa [ENNReal.ofReal_pow] using h4
  have dec : ∀ Y : H →L[ℂ] H, hsNormSq Y = ∑' n, hsNormSq (M.P (I n) ∘L Y) := fun Y => by
    simp only [hsNormSq]
    rw [ENNReal.tsum_comm]
    exact tsum_congr fun m => pyth _
  have un : ∀ t, ‖M.F.U t‖ₑ ≤ 1 := fun t => by
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_le_one]
    exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun h => by rw [M.F.norm, one_mul]
  have step : ∀ n : ℤ, hsNormSq (M.P (I n) ∘L X ∘L M.P (Ioc a b)) ≤ hsNormSq (M.P (I n) ∘L ContinuousLinearMap.adjoint (M.P (Ioc a b) ∘L X)) := fun n => by
    have t1 := ((pl (Ioc a b) _ measurableSet_Ioc (measurableSet_Ioc (a := a) (b := b))).2.2.2.2 (-(n * d))).1
    have pre : (fun x => x + -(n * d)) ⁻¹' Ioc a b = I n := by
      ext x
      simp only [I, mem_preimage, mem_Ioc]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    rw [pre] at t1
    have t2 : ∀ h, M.F.U (-(n * d)) (M.P (Ioc a b) h) = M.P (I n) (M.F.U (-(n * d)) h) := fun h => DFunLike.congr_fun t1 h
    have e : M.P (I n) ∘L X ∘L M.P (Ioc a b) = M.F.U (-(n * d)) ∘L (M.P (Ioc a b) ∘L X ∘L M.P (I n)) ∘L M.F.U (-(n * d)) := by
      ext h
      simp only [ContinuousLinearMap.comp_apply]
      rw [← t2, hX, t2, ← M.F.add, add_neg_cancel, M.F.zero]
    have e2 : M.P (I n) ∘L ContinuousLinearMap.adjoint (M.P (Ioc a b) ∘L X) =
        ContinuousLinearMap.adjoint (M.P (Ioc a b) ∘L X ∘L M.P (I n)) := by
      simp only [ContinuousLinearMap.adjoint_comp, sa _ (hI n), ContinuousLinearMap.comp_assoc]
    rw [e, e2, hsNormSq_adjoint]
    refine (hsNormSq_comp_left_le _ _).trans ((mul_le_of_le_one_left' (pow_le_one' (un _) _)).trans ?_)
    exact (hsNormSq_comp_right_le _ _).trans (mul_le_of_le_one_left' (pow_le_one' (un _) _))
  show hsNormSq _ < _
  rw [dec]
  refine (ENNReal.tsum_le_tsum step).trans_lt ?_
  rw [← dec]
  exact hs.adjoint
