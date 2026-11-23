import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.CuspTrInt
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.IntEst
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KerId
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.NormLeOfSq
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KvCont
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.RopAe
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.QhtBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.QhtTw
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.QmapPres
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalTwistEx

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

set_option maxHeartbeats 800000 in
theorem UpperTheory.ConvolutionTheory.K.kern2 :
    Kern2 := by
  intro K _ _ n μ _ θ a g ha ha' hg hg'
  haveI := Reduction.isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  obtain ⟨C1, N1, hC1, b1⟩ := (kvBd K n μ a).1 ha
  obtain ⟨C2, N2, hC2, b2⟩ := (kvBd K n μ (ccStar g)).1 hg
  obtain ⟨C4, hC4, b4⟩ := (kvBd K n μ (ccStar g)).2 hg' 0
  obtain ⟨D, c, hD, bt⟩ := qhtTw K n μ θ
  obtain ⟨q1, -, qm⟩ := qhtBasic K n
  refine ⟨N1 + c * N2, fun N' => ?_⟩
  obtain ⟨C3, hC3, b3⟩ := (kvBd K n μ a).2 ha' N'
  set v := (quotientMeasure (Gam K n) μ).real Set.univ with hv
  have hv0 : 0 ≤ v := measureReal_nonneg
  refine ⟨v * (C1 * (C2 * D ^ N2) + C3 * C4), fun f M Z hZ hM hf h0 => ?_⟩
  obtain ⟨hi, ht⟩ := cuspTrInt K n μ θ f a g M ha' hg' hM hf
  set Q := M ∘L (ContinuousLinearMap.id ℂ (L2 μ) - Pc μ) with hQ
  have hPP : ∀ u w : L2 μ, ⟪Pc μ u, M (Pc μ w)⟫_ℂ = ⟪u, M (Pc μ w)⟫_ℂ := by
    intro u w
    have e1 : M (Pc μ w) = Pc μ (M w) := DFunLike.congr_fun hM w
    have e2 : Pc μ (Pc μ (M w)) = Pc μ (M w) :=
      Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem _ _)
    rw [e1]
    conv_rhs => rw [← e2]
    exact Submodule.inner_starProjection_left_eq_right _ _ _
  have hsum : ∀ y : RightCosetSpace (Gam K n), twKQ θ f y =
      ⟪Pc μ (kv μ a (Quotient.out y)), M (Pc μ (kv μ (ccStar g) (θ.e (Quotient.out y))))⟫_ℂ +
        ⟪kv μ a (Quotient.out y), Q (kv μ (ccStar g) (θ.e (Quotient.out y)))⟫_ℂ := by
    intro y
    rw [hPP, ← inner_add_right, twKQ, twK, kerId K n μ f a g M hf]
    congr 1
    simp [hQ]
  have hcont : Continuous fun y : RightCosetSpace (Gam K n) =>
      ⟪kv μ a (Quotient.out y), Q (kv μ (ccStar g) (θ.e (Quotient.out y)))⟫_ℂ := by
    refine continuous_coinduced_dom.2 ?_
    have hc : Continuous fun x : G1 K n => ⟪kv μ a x, Q (kv μ (ccStar g) (θ.e x))⟫_ℂ :=
      (kvCont K n μ a).inner (Q.continuous.comp ((kvCont K n μ (ccStar g)).comp θ.e.continuous))
    refine hc.congr fun x => ?_
    obtain ⟨γ, hγ⟩ := mk_eq_mk_iff.1 (show mk (Gam K n) (Quotient.out (mk (Gam K n) x)) = mk (Gam K n) x from Quotient.out_eq _)
    change _ = ⟪kv μ a (Quotient.out (mk (Gam K n) x)), Q (kv μ (ccStar g) (θ.e (Quotient.out (mk (Gam K n) x))))⟫_ℂ
    rw [← hγ]
    change _ = ⟪kv μ a ((γ : G1 K n) * x), Q (kv μ (ccStar g) (θ.e ((γ : G1 K n) * x)))⟫_ℂ
    rw [map_mul, (ropAe K n μ a).2 _ γ.2, (ropAe K n μ (ccStar g)).2 _ ((θ.mem_gam _).2 γ.2)]
  have hZ0 : 0 < Z := lt_of_lt_of_le one_pos hZ
  have est := intEst (quotientMeasure (Gam K n) μ) _ (twKQ θ f) _ _ Z (C1 * (C2 * D ^ N2) * Z ^ (N1 + c * N2) * ‖Q‖)
    (C3 * C4 * (Z ^ N')⁻¹ * ‖M‖) qm hi hcont.aestronglyMeasurable (by positivity) (by positivity) hsum
    (fun y hy => h0 _ hy) (fun y hy => ?_) (fun y hy => ?_)
  · rw [twInt, ht]
    refine est.trans (add_le_add ?_ ?_)
    · have : 0 ≤ v * (C3 * C4) * Z ^ (N1 + c * N2) * ‖Q‖ := by positivity
      calc _ = v * (C1 * (C2 * D ^ N2) + C3 * C4) * Z ^ (N1 + c * N2) * ‖Q‖ - v * (C3 * C4) * Z ^ (N1 + c * N2) * ‖Q‖ := by ring
        _ ≤ _ := sub_le_self _ this
    · have : 0 ≤ v * (C1 * (C2 * D ^ N2)) * (Z ^ N')⁻¹ * ‖M‖ := by positivity
      calc _ = v * (C1 * (C2 * D ^ N2) + C3 * C4) * (Z ^ N')⁻¹ * ‖M‖ - v * (C1 * (C2 * D ^ N2)) * (Z ^ N')⁻¹ * ‖M‖ := by ring
        _ ≤ _ := sub_le_self _ this
  · set x : G1 K n := Quotient.out y
    have hx0 : 0 ≤ qht x := zero_le_one.trans (q1 x)
    have u1 : ‖kv μ a x‖ ≤ C1 * Z ^ N1 := (b1 x).trans (by gcongr)
    have u2 : ‖kv μ (ccStar g) (θ.e x)‖ ≤ C2 * (D * Z ^ c) ^ N2 := by
      refine (b2 _).trans ?_
      have h3 : qht (θ.e x) ≤ D * Z ^ c := (bt x).trans (by gcongr)
      have h4 : 0 ≤ qht (θ.e x) := zero_le_one.trans (q1 _)
      gcongr
    calc _ ≤ ‖kv μ a x‖ * ‖Q (kv μ (ccStar g) (θ.e x))‖ := norm_inner_le_norm _ _
      _ ≤ (C1 * Z ^ N1) * (‖Q‖ * (C2 * (D * Z ^ c) ^ N2)) := by
          refine mul_le_mul u1 ((Q.le_opNorm _).trans ?_) (norm_nonneg _) (by positivity)
          gcongr
      _ = _ := by rw [mul_pow, ← pow_mul, pow_add]; ring
  · set x : G1 K n := Quotient.out y
    have u1 : ‖Pc μ (kv μ a x)‖ ≤ C3 * (Z ^ N')⁻¹ := (b3 x).trans (by gcongr)
    have u2 : ‖Pc μ (kv μ (ccStar g) (θ.e x))‖ ≤ C4 := by simpa using b4 (θ.e x)
    calc _ ≤ ‖Pc μ (kv μ a x)‖ * ‖M (Pc μ (kv μ (ccStar g) (θ.e x)))‖ := norm_inner_le_norm _ _
      _ ≤ (C3 * (Z ^ N')⁻¹) * (‖M‖ * C4) := by
          refine mul_le_mul u1 ((M.le_opNorm _).trans ?_) (norm_nonneg _) (by positivity)
          gcongr
      _ = _ := by ring
