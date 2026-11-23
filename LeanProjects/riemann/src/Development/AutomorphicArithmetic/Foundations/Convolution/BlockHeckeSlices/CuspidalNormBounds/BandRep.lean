import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.DatDatum
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.RepOps
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.AmpRep
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.AmpComm
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.CapZcMemOfE

open NumberField

section SlopeTestRemainingChoices

open MeasureTheory GlobalTheory.CuspRep UpperTheory.ConvolutionTheory.BW UpperTheory.ConvolutionTheory.C

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}

private theorem zop_mul (P Q : MvPolynomial ((E →+* ℂ) × Fin n) ℂ) : zop (P * Q) = zop P * zop Q := by
  simp only [zop, map_mul, MulMemClass.coe_mul]

private theorem zop_one : zop (1 : MvPolynomial ((E →+* ℂ) × Fin n) ℂ) = 1 := by
  simp [zop]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem inv_op (A : H →L[ℂ] H) (hA : 0 ≤ A) (η : ℝ) (hη : 0 < η) (χ : ℝ → ℝ) (hχ : Continuous χ)
    (h0 : ∀ x ≤ η / 2, χ x = 0) :
    ∃ T : H →L[ℂ] H, ‖T‖ ≤ 2 / η ∧ Commute A T ∧ A * T * fcalc χ A = fcalc χ A := by
  have hs : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA
  have hp : 0 < η / 2 := half_pos hη
  have hg : Continuous fun x : ℝ => (max x (η / 2))⁻¹ :=
    (continuous_id.max continuous_const).inv₀ fun x => (lt_of_lt_of_le hp (le_max_right _ _)).ne'
  refine ⟨cfc (fun x : ℝ => (max x (η / 2))⁻¹) A, ?_, ((Commute.refl A).cfc_real _).symm, ?_⟩
  · refine norm_cfc_le (𝕜 := ℝ) (by positivity) fun x _ => ?_
    have h2 : 0 < max x (η / 2) := lt_of_lt_of_le hp (le_max_right _ _)
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 h2), show 2 / η = (η / 2)⁻¹ by rw [inv_div]]
    exact inv_anti₀ hp (le_max_right _ _)
  · have e : χ = fun x => x * (max x (η / 2))⁻¹ * χ x := by
      funext x
      rcases le_or_gt x (η / 2) with h | h
      · simp [h0 x h]
      · rw [max_eq_left h.le, mul_inv_cancel₀ (hp.trans h).ne', one_mul]
    unfold fcalc
    conv_rhs => rw [e]
    rw [cfc_mul (fun x : ℝ => x * (max x (η / 2))⁻¹) χ A (continuous_id.mul hg).continuousOn hχ.continuousOn,
      cfc_mul (fun x : ℝ => x) (fun x : ℝ => (max x (η / 2))⁻¹) A continuous_id.continuousOn hg.continuousOn,
      cfc_id' ℝ A]

private theorem norm_pow_apply_le (T : H →L[ℂ] H) (c : ℝ) (hc : 0 ≤ c) (hT : ‖T‖ ≤ c) (k : ℕ) (v : H) :
    ‖(T ^ k) v‖ ≤ c ^ k * ‖v‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply]
    calc ‖T ((T ^ k) v)‖ ≤ ‖T‖ * ‖(T ^ k) v‖ := T.le_opNorm _
      _ ≤ c * (c ^ k * ‖v‖) := mul_le_mul hT ih (norm_nonneg _) hc
      _ = c ^ (k + 1) * ‖v‖ := by ring

end SlopeTestRemainingChoices

open MeasureTheory GlobalTheory.CuspRep GroundTheory.Automorphic UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.BW UpperTheory.ConvolutionTheory.C in
theorem UpperTheory.ConvolutionTheory.BW.bandRep :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.BandRep E := by
  intro E _ _ _ n μ _ 𝔞 η hn hη
  classical
  obtain ⟨ρ, N, L, hL, hbd, hZ⟩ := UpperTheory.ConvolutionTheory.BW.ampRep E n μ 𝔞 hn
  obtain ⟨h0, -, -, -, hAZ, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.ampComm E n μ 𝔞 fun τ i => (UpperTheory.ConvolutionTheory.Dp.capZc E n τ).1 i
  have uniq : ∀ v φ, Rep μ (𝔞.A v) φ → L v = φ := fun v φ h => (UpperTheory.ConvolutionTheory.BW.repOps E n μ hn _ _ (hL v).1).1 φ h
  have hstep : ∀ x v, zop (MvPolynomial.X x) (L (𝔞.A v)) = L (𝔞.Z x v) := fun x v => by
    refine (uniq _ _ ?_).symm
    have e : 𝔞.A (𝔞.Z x v) = 𝔞.Z x (𝔞.A v) :=
      congrArg (fun T : LL μ →L[ℂ] LL μ => T v) (hAZ x).eq
    rw [e]
    exact hZ x _
  obtain ⟨D, hD0, hD⟩ : ∃ D : ℝ, 0 ≤ D ∧ ∀ x, ‖𝔞.Z x‖ ≤ D :=
    ⟨∑ x : (E →+* ℂ) × Fin n, ‖𝔞.Z x‖, Finset.sum_nonneg fun _ _ => norm_nonneg _, fun x =>
      Finset.single_le_sum (f := fun x : (E →+* ℂ) × Fin n => ‖𝔞.Z x‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ x)⟩
  have hpow : ∀ (k : ℕ) (α : ((E →+* ℂ) × Fin n) →₀ ℕ), α.degree = k → ∀ y : LL μ, ∃ w : LL μ,
      ‖w‖ ≤ D ^ k * ‖y‖ ∧ zop (MvPolynomial.monomial α 1) (L ((𝔞.A ^ k) y)) = L w := by
    intro k
    induction k with
    | zero =>
      intro α hα y
      obtain rfl : α = 0 := (Finsupp.degree_eq_zero_iff α).1 hα
      refine ⟨y, by simp, ?_⟩
      have e : (MvPolynomial.monomial (0 : ((E →+* ℂ) × Fin n) →₀ ℕ) (1 : ℂ)) = 1 := rfl
      rw [e, zop_one]
      simp
    | succ k ih =>
      intro α hα y
      have hne : α ≠ 0 := by
        rintro rfl
        simp at hα
      obtain ⟨x, hx⟩ := Finsupp.support_nonempty_iff.2 hne
      have hle : Finsupp.single x 1 ≤ α :=
        Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hx))
      obtain ⟨β, rfl⟩ := exists_add_of_le hle
      have hβ : β.degree = k := by
        have := hα
        rw [map_add, Finsupp.degree_single] at this
        omega
      obtain ⟨w, hw, hzw⟩ := ih β hβ (𝔞.Z x y)
      refine ⟨w, ?_, ?_⟩
      · calc ‖w‖ ≤ D ^ k * ‖𝔞.Z x y‖ := hw
          _ ≤ D ^ k * (D * ‖y‖) := by
            refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hD0 _)
            exact ((𝔞.Z x).le_opNorm y).trans (mul_le_mul_of_nonneg_right (hD x) (norm_nonneg _))
          _ = D ^ (k + 1) * ‖y‖ := by ring
      · have e1 : (MvPolynomial.monomial (Finsupp.single x 1 + β) (1 : ℂ)) =
            MvPolynomial.monomial β 1 * MvPolynomial.X x := by
          rw [MvPolynomial.X, MvPolynomial.monomial_mul, add_comm, one_mul]
        have e2 : (𝔞.A ^ (k + 1)) y = 𝔞.A ((𝔞.A ^ k) y) := by
          rw [pow_succ', ContinuousLinearMap.mul_apply]
        have e3 : 𝔞.Z x ((𝔞.A ^ k) y) = (𝔞.A ^ k) (𝔞.Z x y) :=
          (congrArg (fun T : LL μ →L[ℂ] LL μ => T y) ((hAZ x).pow_left k).eq).symm
        rw [e1, zop_mul, e2, Module.End.mul_apply, hstep, e3, hzw]
  have hη2 : 0 ≤ 2 / η := by positivity
  refine ⟨D * (2 / η), mul_nonneg hD0 hη2, fun χ hχ hχ0 u φ hrep => ?_⟩
  obtain ⟨T, hT, hAT, hF⟩ := inv_op 𝔞.A h0 η hη χ hχ hχ0
  set v₀ : LL μ := fcalc χ 𝔞.A u with hv₀
  have hv : (𝔞.A * T) v₀ = v₀ := congrArg (fun S : LL μ →L[ℂ] LL μ => S u) hF
  have hpw : ∀ k : ℕ, (𝔞.A ^ k) ((T ^ k) v₀) = v₀ := fun k => by
    rw [← ContinuousLinearMap.mul_apply, ← hAT.mul_pow]
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ContinuousLinearMap.mul_apply, hv, ih]
  have hφ : ∀ k : ℕ, L ((𝔞.A ^ k) ((T ^ (k + 1)) v₀)) = φ := fun k => by
    refine uniq _ _ ?_
    have e : 𝔞.A ((𝔞.A ^ k) ((T ^ (k + 1)) v₀)) = v₀ := by
      rw [← ContinuousLinearMap.mul_apply, ← pow_succ']
      exact hpw (k + 1)
    rw [e]
    exact hrep
  refine { toUmg := hrep.umg, band := ⟨N, fun a => ?_⟩ }
  obtain ⟨B, hB⟩ := hbd a
  refine ⟨|B| * (2 / η) * ‖v₀‖, fun α g => ?_⟩
  obtain ⟨w, hw, hzw⟩ := hpow _ α rfl ((T ^ (α.degree + 1)) v₀)
  rw [← hφ α.degree, hzw]
  have hy := norm_pow_apply_le T (2 / η) hη2 hT (α.degree + 1) v₀
  have hh : 0 ≤ AutomorphicForm.height g ^ N := pow_nonneg (AutomorphicForm.height_pos g).le _
  have hw2 : ‖w‖ ≤ (D * (2 / η)) ^ α.degree * (2 / η) * ‖v₀‖ := by
    calc ‖w‖ ≤ D ^ α.degree * ‖(T ^ (α.degree + 1)) v₀‖ := hw
      _ ≤ D ^ α.degree * ((2 / η) ^ (α.degree + 1) * ‖v₀‖) := mul_le_mul_of_nonneg_left hy (pow_nonneg hD0 _)
      _ = (D * (2 / η)) ^ α.degree * (2 / η) * ‖v₀‖ := by rw [mul_pow, pow_succ]; ring
  calc ‖(UpperTheory.V.Cm.uC E n a (L w)).1 g‖ ≤ B * ‖w‖ * AutomorphicForm.height g ^ N := hB w g
    _ ≤ |B| * ((D * (2 / η)) ^ α.degree * (2 / η) * ‖v₀‖) * AutomorphicForm.height g ^ N := by
      refine mul_le_mul_of_nonneg_right ?_ hh
      exact (mul_le_mul_of_nonneg_right (le_abs_self B) (norm_nonneg w)).trans
        (mul_le_mul_of_nonneg_left hw2 (abs_nonneg B))
    _ = |B| * (2 / η) * ‖v₀‖ * (D * (2 / η)) ^ α.degree * AutomorphicForm.height g ^ N := by ring
