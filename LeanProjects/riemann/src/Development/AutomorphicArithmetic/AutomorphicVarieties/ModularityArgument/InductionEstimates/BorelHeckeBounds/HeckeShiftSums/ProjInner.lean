import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.Full
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.SfiniteOfFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.OmBdReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.OmMeas
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.CtVanish
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.CuspTrInt
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.IntEst
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KerId
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.NormLeOfSq
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KvCont
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.RopAe
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.QhtTw
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.QhtBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.QmapPres
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.PolyBdAll
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SmoothDecay

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

private theorem proj_inner {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P M : H →L[ℂ] H) (hs : IsSelfAdjoint P) (hi : P ∘L P = P) (hM : M ∘L P = P ∘L M) (u w : H) :
    ⟪P u, M (P w)⟫_ℂ = ⟪u, M (P w)⟫_ℂ := by
  have e1 : M (P w) = P (M w) := DFunLike.congr_fun hM w
  have e2 : P (P (M w)) = P (M w) := DFunLike.congr_fun hi (M w)
  have e3 : ⟪P u, P (M w)⟫_ℂ = ⟪u, P (P (M w))⟫_ℂ := hs.isSymmetric u (P (M w))
  rw [e1, e3, e2]

private theorem pc_inner {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    (M : L2 μ →L[ℂ] L2 μ) (hM : M ∘L Pc μ = Pc μ ∘L M) (u w : L2 μ) :
    ⟪Pc μ u, M (Pc μ w)⟫_ℂ = ⟪u, M (Pc μ w)⟫_ℂ := by
  have e1 : M (Pc μ w) = Pc μ (M w) := DFunLike.congr_fun hM w
  have e2 : Pc μ (Pc μ (M w)) = Pc μ (M w) :=
    Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem _ _)
  rw [e1]
  conv_rhs => rw [← e2]
  exact Submodule.inner_starProjection_left_eq_right _ _ _

private theorem ker_cont {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    (θ : Twist μ) (a b : CC K n) (Q : L2 μ →L[ℂ] L2 μ) :
    Continuous fun y : RightCosetSpace (Gam K n) =>
      ⟪UpperTheory.ConvolutionTheory.K.kv μ a (Quotient.out y), Q (UpperTheory.ConvolutionTheory.K.kv μ b (θ.e (Quotient.out y)))⟫_ℂ := by
  refine continuous_coinduced_dom.2 ?_
  have hc : Continuous fun x : G1 K n => ⟪UpperTheory.ConvolutionTheory.K.kv μ a x, Q (UpperTheory.ConvolutionTheory.K.kv μ b (θ.e x))⟫_ℂ :=
    (kvCont K n μ a).inner (Q.continuous.comp ((kvCont K n μ b).comp θ.e.continuous))
  refine hc.congr fun x => ?_
  obtain ⟨γ, hγ⟩ := mk_eq_mk_iff.1 (show mk (Gam K n) (Quotient.out (mk (Gam K n) x)) = mk (Gam K n) x from Quotient.out_eq _)
  change _ = ⟪UpperTheory.ConvolutionTheory.K.kv μ a (Quotient.out (mk (Gam K n) x)), Q (UpperTheory.ConvolutionTheory.K.kv μ b (θ.e (Quotient.out (mk (Gam K n) x))))⟫_ℂ
  rw [← hγ]
  change _ = ⟪UpperTheory.ConvolutionTheory.K.kv μ a ((γ : G1 K n) * x), Q (UpperTheory.ConvolutionTheory.K.kv μ b (θ.e ((γ : G1 K n) * x)))⟫_ℂ
  rw [map_mul, (ropAe K n μ a).2 _ γ.2, (ropAe K n μ b).2 _ ((θ.mem_gam _).2 γ.2)]

set_option maxHeartbeats 1000000 in
private theorem ker_bd {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    (θ : Twist μ) (a b : CC K n) : ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ (Q : L2 μ →L[ℂ] L2 μ) (x : G1 K n) (Z : ℝ), qht x ≤ Z →
      ‖⟪UpperTheory.ConvolutionTheory.K.kv μ a x, Q (UpperTheory.ConvolutionTheory.K.kv μ b (θ.e x))⟫_ℂ‖ ≤ C * Z ^ N * ‖Q‖ := by
  obtain ⟨C1, N1, hC1, b1⟩ := (kvBd K n μ a).1 (polyBdAll K n μ a)
  obtain ⟨C2, N2, hC2, b2⟩ := (kvBd K n μ b).1 (polyBdAll K n μ b)
  obtain ⟨D, c, hD, bt⟩ := qhtTw K n μ θ
  obtain ⟨q1, -, -⟩ := qhtBasic K n
  refine ⟨C1 * (C2 * D ^ N2), N1 + c * N2, by positivity, fun Q x Z hy => ?_⟩
  have hx0 : 0 ≤ qht x := zero_le_one.trans (q1 x)
  have hZ : 0 ≤ Z := hx0.trans hy
  have u1 : ‖UpperTheory.ConvolutionTheory.K.kv μ a x‖ ≤ C1 * Z ^ N1 := (b1 x).trans (by gcongr)
  have u2 : ‖UpperTheory.ConvolutionTheory.K.kv μ b (θ.e x)‖ ≤ C2 * (D * Z ^ c) ^ N2 := by
    refine (b2 _).trans ?_
    have h3 : qht (θ.e x) ≤ D * Z ^ c := (bt x).trans (by gcongr)
    have h4 : 0 ≤ qht (θ.e x) := zero_le_one.trans (q1 _)
    gcongr
  calc _ ≤ ‖UpperTheory.ConvolutionTheory.K.kv μ a x‖ * ‖Q (UpperTheory.ConvolutionTheory.K.kv μ b (θ.e x))‖ := norm_inner_le_norm _ _
    _ ≤ (C1 * Z ^ N1) * (‖Q‖ * (C2 * (D * Z ^ c) ^ N2)) := by
        refine mul_le_mul u1 ((Q.le_opNorm _).trans ?_) (norm_nonneg _) (by positivity)
        gcongr
    _ = _ := by rw [mul_pow, ← pow_mul, pow_add]; ring

private theorem cusp_bd {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    (a b : CC K n) (ha : CuspDecay μ a) (hb : CuspDecay μ b) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : L2 μ →L[ℂ] L2 μ) (x x' : G1 K n),
      ‖⟪Pc μ (UpperTheory.ConvolutionTheory.K.kv μ a x), M (Pc μ (UpperTheory.ConvolutionTheory.K.kv μ b x'))⟫_ℂ‖ ≤ C * (qht x ^ m)⁻¹ * ‖M‖ := by
  obtain ⟨C4, hC4, b4⟩ := (kvBd K n μ b).2 hb 0
  obtain ⟨C3, hC3, b3⟩ := (kvBd K n μ a).2 ha m
  obtain ⟨q1, -, -⟩ := qhtBasic K n
  refine ⟨C3 * C4, by positivity, fun M x x' => ?_⟩
  have hx0 : 0 ≤ qht x := zero_le_one.trans (q1 x)
  have u2 : ‖Pc μ (UpperTheory.ConvolutionTheory.K.kv μ b x')‖ ≤ C4 := by simpa using b4 x'
  calc _ ≤ ‖Pc μ (UpperTheory.ConvolutionTheory.K.kv μ a x)‖ * ‖M (Pc μ (UpperTheory.ConvolutionTheory.K.kv μ b x'))‖ := norm_inner_le_norm _ _
    _ ≤ (C3 * (qht x ^ m)⁻¹) * (‖M‖ * C4) := by
        refine mul_le_mul (b3 x) ((M.le_opNorm _).trans ?_) (norm_nonneg _) (by positivity)
        gcongr
    _ = _ := by ring

private theorem decay {c C T q : ℝ} {m N' : ℕ} (hc : 0 < c) (hT : 2 * C / c + 1 ≤ T) (hT0 : 0 ≤ T) (hm : 2 * N' / c ≤ m)
    (hq : Real.exp (c * T - C) ≤ q) : Real.exp (c / 2 * T) < q ∧ (q ^ m)⁻¹ ≤ Real.exp (-(N' * T)) := by
  have h1 : 2 * C / c < T := by linarith
  rw [div_lt_iff₀ hc] at h1
  rw [div_le_iff₀ hc] at hm
  have h2 : Real.exp (c / 2 * T) < q := lt_of_lt_of_le (Real.exp_lt_exp.2 (by linarith)) hq
  refine ⟨h2, ?_⟩
  rw [Real.exp_neg]
  refine inv_anti₀ (Real.exp_pos _) ?_
  calc Real.exp (N' * T) ≤ Real.exp (m * (c / 2 * T)) := Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_right hm hT0])
    _ = Real.exp (c / 2 * T) ^ m := Real.exp_nat_mul _ _
    _ ≤ q ^ m := pow_le_pow_left₀ (Real.exp_pos _).le h2.le m

private theorem intEst' {X : Type} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] (S : Set X) (k c w : X → ℂ) (A B : ℝ)
    (hS : MeasurableSet S) (hc : Integrable c ν) (hw : Integrable w ν) (hk : AEStronglyMeasurable k ν) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h0 : ∀ x, x ∉ S → k x = 0) (h1 : ∀ x, x ∈ S → ‖k x - c x - w x‖ ≤ A) (h2 : ∀ x, x ∉ S → ‖c x + w x‖ ≤ B) :
    ‖∫ x, k x ∂ν - ∫ x, c x ∂ν - ∫ x, w x ∂ν‖ ≤ ν.real Set.univ * A + ν.real Set.univ * B := by
  have hh : ∀ x, (1 / 2 : ℝ) < Sᶜ.indicator (fun _ => (1 : ℝ)) x ↔ x ∉ S := fun x => by
    by_cases hx : x ∈ S
    · simp [hx]
    · simp [hx]; norm_num
  have := intEst ν (Sᶜ.indicator fun _ => (1 : ℝ)) k (fun x => c x + w x) (fun x => k x - c x - w x) (1 / 2) A B
    (measurable_const.indicator hS.compl) (hc.add hw) ((hk.sub hc.1).sub hw.1) hA hB (fun x => by ring)
    (fun x hx => h0 x ((hh x).1 hx)) (fun x hx => h1 x (by by_contra h; exact absurd ((hh x).2 h) (not_lt.2 hx)))
    (fun x hx => h2 x ((hh x).1 hx))
  rwa [integral_add hc hw, ← sub_sub] at this

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.kernX :
    KernX := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hp D d d' A A' θ a g P hP hθ hΛθ ha haD hg hgD
  haveI := Reduction.isFiniteMeasure_quotientMeasure (K := K) (n := 2 + 2) μ
  obtain ⟨C0, c, N0, hc, hC0, hom⟩ := omBd (K := K)
  obtain ⟨C1, N1, hC1, b1⟩ := ker_bd μ θ a (CuspidalProjection.ccStar g)
  have ha' := smoothDecay K (2 + 2) μ a ha
  have hg' := smoothDecay K (2 + 2) μ _ hg
  refine ⟨c / 2, half_pos hc, N0 * N1, fun N' => ?_⟩
  obtain ⟨m, hm⟩ := exists_nat_ge (2 * (N' : ℝ) / c)
  obtain ⟨C2, hC2, b2⟩ := cusp_bd μ a _ ha' hg' m
  obtain ⟨C3, hC3, b3⟩ := famTr K μ μ₂ τ₁ τ₂ hp D d d' A A' θ a g P hP hθ hΛθ ha haD hg hgD m
  set v := (quotientMeasure (Gam K (2 + 2)) μ).real Set.univ with hv
  have hv0 : 0 ≤ v := measureReal_nonneg
  refine ⟨v * (C1 * C0 ^ N1 + (C2 + C3)), 2 * C0 / c + 1, fun f M Λ T hT hT0 hM hMP hf hΛ h0 => ?_⟩
  obtain ⟨htc, w, hw, htr, hw1, hw2⟩ := b3 f M Λ T hT0 hMP hf hΛ
  refine ⟨htc, ?_⟩
  obtain ⟨hi, ht⟩ := cuspTrInt K (2 + 2) μ θ f a g M ha' hg' hM hf
  have hk : twKQ θ f = fun y : RightCosetSpace (Gam K (2 + 2)) =>
      ⟪UpperTheory.ConvolutionTheory.K.kv μ a (Quotient.out y), M (UpperTheory.ConvolutionTheory.K.kv μ (CuspidalProjection.ccStar g) (θ.e (Quotient.out y)))⟫_ℂ := by
    funext y
    rw [twKQ, twK, kerId K (2 + 2) μ f a g M hf]
  have est := intEst' (quotientMeasure (Gam K (2 + 2)) μ) _ (twKQ θ f) _ w
    (C1 * C0 ^ N1 * Real.exp ((N0 * N1 : ℕ) * T) * ‖M ∘L (1 - Pc μ - P)‖) ((C2 + C3) * Real.exp (-(N' * T)) * ‖M‖)
    (omMeas (K := K) T).2.2 hi hw (by rw [hk]; exact (ker_cont μ θ a _ M).aestronglyMeasurable) (by positivity) (by positivity)
    (fun y hy => h0 _ (decay hc hT hT0 hm ((hom T _ hT0).2 hy)).1) (fun y hy => ?_) (fun y hy => ?_)
  · rw [twInt, ht, htr]
    refine est.trans (add_le_add ?_ ?_)
    · rw [← mul_assoc, ← mul_assoc]
      gcongr
      have : 0 ≤ C2 + C3 := by positivity
      linarith
    · rw [← mul_assoc, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hv0) (Real.exp_pos _).le) (norm_nonneg _)
      have : 0 ≤ C1 * C0 ^ N1 := by positivity
      linarith
  · have e := b1 (M ∘L (1 - Pc μ - P)) (Quotient.out y) _ ((hom T _ hT0).1 hy)
    rw [mul_pow, ← Real.exp_nat_mul, ← mul_assoc, show (N1 : ℝ) * (N0 * T) = (N0 * N1 : ℕ) * T by push_cast; ring] at e
    refine le_of_eq_of_le ?_ e
    rw [hw1 y hy, hk, pc_inner μ M hM, proj_inner P M hP.1 hP.2.1 hMP, ← inner_sub_right, ← inner_sub_right]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, map_sub]
  · have e := (decay hc hT hT0 hm ((hom T _ hT0).2 hy)).2
    refine (norm_add_le _ _).trans ((add_le_add (b2 M _ _) (hw2 y hy)).trans ?_)
    rw [← add_mul, ← add_mul]
    gcongr
