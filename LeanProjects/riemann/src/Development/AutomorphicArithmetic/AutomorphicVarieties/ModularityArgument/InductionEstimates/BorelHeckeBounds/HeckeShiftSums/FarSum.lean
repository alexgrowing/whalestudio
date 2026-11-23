import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.Full
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.SecDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.SgBasics
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SumField
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpqMinor
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PkLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.QhtBasic

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

private theorem fs_ratio (ρ : Fin (2 + 2) → ℝ) (hρ : ∀ i, 0 < ρ i) (t C H d : ℝ) (ht : 0 < t) (hd : 1 ≤ d) (hH : 0 ≤ H)
    (hr : Rel t ρ) (h1 : |H - d * Real.log (ρ 0 * ρ 1)| ≤ C) (h2 : |Real.log (ρ 0 * ρ 1 * (ρ 2 * ρ 3))| ≤ C) (i j : Fin (2 + 2)) :
    ρ i / ρ j ≤ Real.exp (2 * C + |Real.log t|) * Real.exp H * max 1 (inR ρ) := by
  have p0 := hρ 0
  have p1 := hρ 1
  have p2 := hρ 2
  have p3 := hρ 3
  have hm : 0 < max 1 (inR ρ) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hM0 : 0 ≤ Real.log (max 1 (inR ρ)) := Real.log_nonneg (le_max_left _ _)
  have hL : Real.log (ρ 0) - Real.log (ρ 1) + (Real.log (ρ 2) - Real.log (ρ 3)) ≤ Real.log (max 1 (inR ρ)) := by
    rw [← Real.log_div p0.ne' p1.ne', ← Real.log_div p2.ne' p3.ne', ← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log (by positivity) (le_max_right _ _)
  have r1 := Real.log_le_log (by positivity) hr.1
  have r2 := Real.log_le_log (by positivity) hr.2
  rw [Real.log_mul ht.ne' p1.ne'] at r1
  rw [Real.log_mul ht.ne' p3.ne'] at r2
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul p0.ne' p1.ne', Real.log_mul p2.ne' p3.ne', abs_le] at h2
  rw [Real.log_mul p0.ne' p1.ne', abs_le] at h1
  have hτ := neg_abs_le (Real.log t)
  have hτ0 := abs_nonneg (Real.log t)
  have hs : -C ≤ Real.log (ρ 0) + Real.log (ρ 1) ∧ Real.log (ρ 0) + Real.log (ρ 1) ≤ H + C := by
    rcases le_total 0 (Real.log (ρ 0) + Real.log (ρ 1)) with h | h
    · have := mul_le_mul_of_nonneg_right hd h
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    · have := mul_le_mul_of_nonpos_right hd h
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hb : ∀ k : Fin (2 + 2), |Real.log (ρ k)| ≤ (2 * C + |Real.log t| + H + Real.log (max 1 (inR ρ))) / 2 := by
    have hk : ∀ k : Fin (2 + 2), k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by decide
    intro k
    rw [abs_le]
    rcases hk k with rfl | rfl | rfl | rfl <;> constructor <;> linarith [hs.1, hs.2, h2.1, h2.2]
  have e : ρ i / ρ j = Real.exp (Real.log (ρ i) - Real.log (ρ j)) := by
    rw [Real.exp_sub, Real.exp_log (hρ i), Real.exp_log (hρ j)]
  rw [e, ← Real.exp_log hm, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  linarith [(abs_le.1 (hb i)).2, (abs_le.1 (hb j)).1]

private theorem fs_point {K : Type} [Field K] [NumberField K] (ω : Set (AdelicGLn.AdelicGL K (2 + 2))) (t : ℝ) (hω : Bor ω)
    (ht : 0 < t) (f : G1 K (2 + 2) → ℂ) (hf : SFun f) (N₀ : ℕ) :
    ∃ N₁ : ℕ, ∀ M : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ (ρ : Fin (2 + 2) → ℝ) (z : G1 K (2 + 2)), Sg ω ρ z → Rel t ρ → 0 ≤ HH z →
      Real.exp (2 * HH z) * ‖f z‖ * AutomorphicForm.height (z : AdelicGLn.AdelicGL K (2 + 2)) ^ N₀ * max 1 (inR ρ) ^ M ≤
        D * qht z ^ N₁ := by
  obtain ⟨C, c, hC, hs⟩ := sgBasics ω hω
  obtain ⟨c₀, C₀, hc₀, hq⟩ := hpQht (K := K)
  refine ⟨⌈c₀⌉₊ * (2 + c * N₀), fun M => ?_⟩
  obtain ⟨D₀, hD₀⟩ := secDec ω t hω ht f hf 0
  obtain ⟨D₁, hD₁⟩ := secDec ω t hω ht f hf (c * N₀ + M)
  set A := Real.exp (2 * C + |Real.log t|) with hA
  have hA1 : 1 ≤ A := Real.one_le_exp (by have := abs_nonneg (Real.log t); linarith)
  refine ⟨(C * A ^ c) ^ N₀ * max 0 (max D₀ D₁) * Real.exp C₀ ^ (2 + c * N₀), by positivity, fun ρ z hz hr hH => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hs ρ z hz
  have hd : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  set m := max 1 (inR ρ) with hm
  have hm1 : 1 ≤ m := le_max_left _ _
  set E := Real.exp (HH z) with hE
  have hE1 : 1 ≤ E := Real.one_le_exp hH
  have h4 := h3 (A * E * m) (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hA1 hE1) hm1)
    (fs_ratio ρ hz.1 t C (HH z) _ ht hd hH hr h1 h2)
  have hQ : 1 ≤ qht z := (qhtBasic K (2 + 2)).1 z
  have h5 : E ≤ Real.exp C₀ * qht z ^ ⌈c₀⌉₊ := by
    rw [← Real.exp_log (lt_of_lt_of_le one_pos hQ), ← Real.exp_nat_mul, ← Real.exp_add, hE, Real.exp_le_exp]
    have := mul_le_mul_of_nonneg_right (Nat.le_ceil c₀) (Real.log_nonneg hQ)
    linarith [hq z]
  have h6 : ‖f z‖ * m ^ (c * N₀ + M) ≤ max 0 (max D₀ D₁) := by
    refine le_trans ?_ (le_max_right _ _)
    rcases le_total 1 (inR ρ) with h | h
    · rw [hm, max_eq_right h]
      exact (hD₁ ρ z hz hr).trans (le_max_right _ _)
    · rw [hm, max_eq_left h, one_pow, ← pow_zero (inR ρ)]
      exact (hD₀ ρ z hz hr).trans (le_max_left _ _)
  have e2 : Real.exp (2 * HH z) = E ^ 2 := by rw [hE, ← Real.exp_nat_mul]; norm_num
  have hh0 := (height_pos (z : AdelicGLn.AdelicGL K (2 + 2))).le
  calc Real.exp (2 * HH z) * ‖f z‖ * AutomorphicForm.height (z : AdelicGLn.AdelicGL K (2 + 2)) ^ N₀ * m ^ M
      ≤ E ^ 2 * ‖f z‖ * (C * (A * E * m) ^ c) ^ N₀ * m ^ M := by rw [e2]; gcongr
    _ = (C * A ^ c) ^ N₀ * (‖f z‖ * m ^ (c * N₀ + M)) * E ^ (2 + c * N₀) := by ring
    _ ≤ (C * A ^ c) ^ N₀ * max 0 (max D₀ D₁) * (Real.exp C₀ * qht z ^ ⌈c₀⌉₊) ^ (2 + c * N₀) := by gcongr
    _ = _ := by rw [mul_pow (Real.exp C₀), ← pow_mul, mul_assoc _ _ (qht z ^ _)]

private theorem fs_sum {K : Type} [Field K] [NumberField K] : ∃ (N₀ : ℕ) (C : ℝ), ∀ (x : G1 K (2 + 2)) (S : Finset (Cos K))
    (g : Cos K → ℝ) (B : ℝ), 0 ≤ B →
    (∀ q ∈ S, ∃ δ ∈ PK K, g q * AutomorphicForm.height ((δ * qx q x : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) ^ N₀ ≤ B) →
    ∑ q ∈ S, g q ≤ C * B := by
  classical
  obtain ⟨N, C, hC, hs⟩ := sumHt (K := K) (2 + 2)
  refine ⟨N, C.toReal, fun x S g B hB h => ?_⟩
  set φ : Gam K (2 + 2) → ℝ := fun γ =>
    (AutomorphicForm.height (((γ : G1 K (2 + 2)) * x : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) ^ N)⁻¹ with hφ
  have hφ0 : ∀ γ, 0 ≤ φ γ := fun γ => inv_nonneg.2 (pow_nonneg (height_pos _).le _)
  have h' : ∀ q : Cos K, ∃ γ : Gam K (2 + 2), (Quotient.mk _ γ : Cos K) = q ∧ (q ∈ S → g q ≤ φ γ * B) := by
    intro q
    by_cases hq : q ∈ S
    · obtain ⟨_, ⟨δ, hδ, rfl⟩, hb⟩ := h q hq
      refine ⟨δ * q.out, ?_, fun _ => ?_⟩
      · refine Eq.trans (Quotient.sound ?_) (Quotient.out_eq q)
        change QuotientGroup.rightRel _ _ _
        rw [QuotientGroup.rightRel_apply]
        simpa using hδ
      · rw [hφ]
        beta_reduce
        rw [le_inv_mul_iff₀ (pow_pos (height_pos _) _), mul_comm, Subgroup.coe_mul (Gam K (2 + 2)), mul_assoc]
        exact hb
    · exact ⟨q.out, Quotient.out_eq q, fun h => absurd h hq⟩
  choose γ hγ hg using h'
  have hinj : Function.Injective γ := fun a b e => by rw [← hγ a, ← hγ b, e]
  have h1 : ∑ q ∈ S, φ (γ q) ≤ C.toReal := by
    rw [← ENNReal.ofReal_le_iff_le_toReal hC, ENNReal.ofReal_sum_of_nonneg fun q _ => hφ0 _,
      ← Finset.sum_image (f := fun a => ENNReal.ofReal (φ a)) fun a _ b _ e => hinj e]
    exact (ENNReal.sum_le_tsum _).trans (hs x)
  calc ∑ q ∈ S, g q ≤ ∑ q ∈ S, φ (γ q) * B := Finset.sum_le_sum fun q hq => hg q hq
    _ = (∑ q ∈ S, φ (γ q)) * B := (Finset.sum_mul _ _ _).symm
    _ ≤ C.toReal * B := mul_le_mul_of_nonneg_right h1 hB

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.farSum :
    ∀ {K : Type} [Field K] [NumberField K] (ω : Set (AdelicGLn.AdelicGL K (2 + 2))) (t : ℝ), Red ω t → ∀ f : G1 K (2 + 2) → ℂ, SFun f →
      (∃ (C : ℝ) (N : ℕ), ∀ (x : G1 K (2 + 2)) (S : Finset (Cos K)), (∀ q ∈ S, 0 ≤ HH (qx q x)) →
        ∑ q ∈ S, Real.exp (2 * HH (qx q x)) * ‖f (qx q x)‖ ≤ C * qht x ^ N) ∧
      ∀ (ε : ℝ) (N' : ℕ), 0 < ε → ∃ C : ℝ, ∀ (x : G1 K (2 + 2)) (S : Finset (Cos K)), (∀ q ∈ S, 0 ≤ HH (qx q x) ∧ Far ω t ε (qx q x)) →
        ∑ q ∈ S, Real.exp (2 * HH (qx q x)) * ‖f (qx q x)‖ ≤ C * (qht x ^ N')⁻¹ := by
  intro K _ _ ω t hred f hf
  obtain ⟨N₀, C, hsum⟩ := fs_sum (K := K)
  obtain ⟨N₁, hp⟩ := fs_point ω t hred.bor hred.pos f hf N₀
  obtain ⟨hq1, hq2, -⟩ := qhtBasic K (2 + 2)
  have hqx : ∀ (q : Cos K) (x : G1 K (2 + 2)), qht (qx q x) = qht x := fun q x => hq2 _ q.out.2 x
  have hqδ : ∀ δ ∈ PK K, ∀ z : G1 K (2 + 2), qht (δ * z) = qht z := by
    rintro _ ⟨δ, -, rfl⟩ z
    exact hq2 _ δ.2 z
  have hH := (hpSpec (K := K)).2.2.1
  refine ⟨?_, fun ε N' hε => ?_⟩
  · obtain ⟨D, hD, h⟩ := hp 0
    refine ⟨C * D, N₁, fun x S hS => ?_⟩
    rw [mul_assoc]
    refine hsum x S _ _ (mul_nonneg hD (pow_nonneg (zero_le_one.trans (hq1 x)) _)) fun q hq => ?_
    obtain ⟨δ, hδ, ρ, h1, h2⟩ := hred.rel (qx q x)
    have h3 := h ρ _ h1 h2 (by rw [hH δ hδ]; exact hS q hq)
    rw [pow_zero, mul_one, hH δ hδ, hf.rat δ hδ, hqδ δ hδ, hqx] at h3
    exact ⟨δ, hδ, h3⟩
  · obtain ⟨D, hD, h⟩ := hp ⌈((N₁ + N' : ℕ) : ℝ) / ε⌉₊
    refine ⟨C * D, fun x S hS => ?_⟩
    rw [mul_assoc]
    have hx0 : 0 < qht x := one_pos.trans_le (hq1 x)
    refine hsum x S _ _ (by positivity) fun q hq => ?_
    obtain ⟨h0, δ, hδ, ρ, h1, h2, h4⟩ := hS q hq
    have h3 := h ρ _ h1 h2 (by rw [hH δ hδ]; exact h0)
    rw [hH δ hδ, hf.rat δ hδ, hqδ δ hδ, hqx] at h3
    rw [hqx] at h4
    refine ⟨δ, hδ, ?_⟩
    have h5 : qht x ^ (N₁ + N') ≤ max 1 (inR ρ) ^ ⌈((N₁ + N' : ℕ) : ℝ) / ε⌉₊ := by
      refine le_trans ?_ (pow_le_pow_left₀ (Real.rpow_nonneg hx0.le ε) (h4.trans (le_max_right _ _)) _)
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      refine Real.rpow_le_rpow_of_exponent_le (hq1 x) ?_
      rw [mul_comm, ← div_le_iff₀ hε]
      exact Nat.le_ceil _
    have hh0 := (height_pos ((δ * qx q x : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2))).le
    have h6 := (mul_le_mul_of_nonneg_left h5 (by positivity)).trans h3
    rw [pow_add, mul_comm (qht x ^ N₁), ← mul_assoc, mul_le_mul_iff_left₀ (pow_pos hx0 _)] at h6
    rwa [← div_eq_mul_inv, le_div_iff₀ (pow_pos hx0 _)]
