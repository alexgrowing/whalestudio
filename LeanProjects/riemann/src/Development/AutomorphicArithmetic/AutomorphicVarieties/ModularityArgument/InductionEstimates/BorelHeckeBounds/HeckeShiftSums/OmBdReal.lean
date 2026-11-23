import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.Full
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.SgBasics
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PkLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpqMinor
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.BlkCont
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.QhtBasic

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

private theorem omBd_real (a : Fin (2 + 2) → ℝ) (s C T : ℝ) (hs : 0 ≤ s) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (h0 : a 1 ≤ a 0 + s) (h1 : a 2 ≤ a 1 + s) (h2 : a 3 ≤ a 2 + s) (h3 : a 0 + a 1 ≤ T + C)
    (h4 : -C ≤ a 0 + a 1 + (a 2 + a 3)) (i j : Fin (2 + 2)) : a i - a j ≤ 4 * T + 20 * (C + s) := by
  have key : ∀ i : Fin (2 + 2), a i ≤ 2 * T + 10 * (C + s) ∧ -(2 * T + 10 * (C + s)) ≤ a i := by
    intro i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by revert i; decide
    rcases hi with rfl | rfl | rfl | rfl <;> constructor <;> linarith
  linarith [(key i).1, (key j).2]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.omBd :
    ∀ {K : Type} [Field K] [NumberField K], ∃ (C c : ℝ) (N : ℕ), 0 < c ∧ 0 ≤ C ∧ ∀ (T : ℝ) (x : G1 K (2 + 2)), 0 ≤ T → (Om T x → qht x ≤ C * Real.exp (N * T)) ∧ (¬ Om T x → Real.exp (c * T - C) ≤ qht x) := by
  intro K _ _
  obtain ⟨ω, t, hred⟩ := redEx (K := K)
  obtain ⟨C, c, hC, hsg⟩ := sgBasics ω hred.bor
  obtain ⟨c', C', hc', hq⟩ := hpQht (K := K)
  obtain ⟨hq1, hqinv, -⟩ := qhtBasic K (2 + 2)
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  set s : ℝ := |Real.log t| with hsdef
  have hs : 0 ≤ s := abs_nonneg _
  set A : ℝ := C * Real.exp (c * (20 * (C + s))) with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨A + |C' / c'|, c'⁻¹, 4 * c, inv_pos.2 hc', by positivity, fun T x hT => ⟨fun hom => ?_, fun hom => ?_⟩⟩
  · obtain ⟨γ, hγ, ρ, hS, hF⟩ := hred.full x
    obtain ⟨h1, h2, h3⟩ := hsg ρ _ hS
    obtain ⟨hρ, -⟩ := hS
    have hH : HH (γ * x) ≤ T := by
      obtain ⟨δ, hδ, e⟩ := (pkLaws (K := K)).2.2.2 ⟨γ, hγ⟩
      have h := hom (Quotient.mk _ ⟨γ, hγ⟩)
      unfold qx at h
      rw [e, mul_assoc, (hpSpec (K := K)).2.2.1 δ hδ] at h
      exact h
    have hd : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by
      exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))
    have hL : Real.log (ρ 0 * ρ 1) ≤ T + C := by
      have h4 := (abs_le.1 h1).1
      rcases le_total 0 (Real.log (ρ 0 * ρ 1)) with h | h
      · nlinarith
      · linarith
    have hstep : ∀ i j : Fin (2 + 2), (j : ℕ) = i + 1 → Real.log (ρ j) ≤ Real.log (ρ i) + s := by
      intro i j hij
      have h := Real.log_le_log (mul_pos hred.pos (hρ j)) (hF i j hij)
      rw [Real.log_mul hred.pos.ne' (hρ j).ne'] at h
      linarith [neg_abs_le (Real.log t)]
    rw [Real.log_mul (mul_pos (hρ 0) (hρ 1)).ne' (mul_pos (hρ 2) (hρ 3)).ne', Real.log_mul (hρ 0).ne' (hρ 1).ne',
      Real.log_mul (hρ 2).ne' (hρ 3).ne'] at h2
    rw [Real.log_mul (hρ 0).ne' (hρ 1).ne'] at hL
    have hR := omBd_real (fun i => Real.log (ρ i)) s C T hs hC0 hT (hstep 0 1 rfl) (hstep 1 2 rfl) (hstep 2 3 rfl) hL
      (abs_le.1 h2).1
    have h5 := h3 (Real.exp (4 * T + 20 * (C + s))) (Real.one_le_exp (by positivity)) fun i j => by
      rw [← Real.exp_log (div_pos (hρ i) (hρ j)), Real.log_div (hρ i).ne' (hρ j).ne']
      exact Real.exp_le_exp.2 (hR i j)
    have h6 : qht x ≤ AutomorphicForm.height ((γ * x : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) :=
      ciInf_le (f := fun δ : Gam K (2 + 2) =>
        AutomorphicForm.height (((δ : G1 K (2 + 2)) * x : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)))
        ⟨0, by rintro _ ⟨δ, rfl⟩; exact (height_pos _).le⟩ ⟨γ, hγ⟩
    have h7 : C * Real.exp (4 * T + 20 * (C + s)) ^ c = A * Real.exp (((4 * c : ℕ) : ℝ) * T) := by
      rw [hA, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
      congr 2
      push_cast
      ring
    refine h6.trans (h5.trans ?_)
    rw [h7]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (abs_nonneg _)) (Real.exp_pos _).le
  · unfold Om at hom
    push Not at hom
    obtain ⟨q, hq'⟩ := hom
    have h1 := hq (qx q x)
    have h2 : qht (qx q x) = qht x := hqinv _ (q.out : Gam K (2 + 2)).2 x
    rw [h2] at h1
    rw [← Real.le_log_iff_exp_le (zero_lt_one.trans_le (hq1 x))]
    have h3 : (T - C') / c' ≤ Real.log (qht x) := by
      rw [div_le_iff₀ hc']
      linarith
    rw [sub_div, div_eq_inv_mul T] at h3
    linarith [le_abs_self (C' / c')]
