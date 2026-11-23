import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.TraceId
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.TraceFar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.BandTC
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CorLim
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.TailB
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Planch
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.KvSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvAdj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.AvApprox

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.traceSm :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (N : W ≃ₗᵢ[ℂ] V), M.IsN (N.toLinearEquiv : W →ₗ[ℂ] V) → ∀ (X : H →L[ℂ] H) (κ : ℝ → V →L[ℂ] W), Ker κ → M.Carries X κ → ∀ (ψ : ℝ → ℝ) (δ T K : ℝ), δ ≤ 1 / 2 → Bump ψ (-δ) 0 → M.T₀ ≤ T →
      IsTraceClass (M.abelian₂ T T ∘L X ∘L M.abelian₂ T T) → (∀ z : ℂ, |z.re| ≤ 1 → ‖symb κ z‖ ≤ K / (1 + |z.im|)) →
      ‖trace (M.abelian₂ T T ∘L (M.F.av (fun t => (ψ t : ℂ)) ∘L X) ∘L M.abelian₂ T T) -
          (1 / 2 : ℂ) * LinearMap.trace ℂ V ((N.toLinearEquiv : W →ₗ[ℂ] V) ∘ₗ (symb κ 0 : V →ₗ[ℂ] W))‖ ≤
        Module.finrank ℂ V * Real.exp (2 * M.T₀) * K * Real.exp (-2 * T) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M N hN X κ hk hX ψ δ T K hδ hψ hT htc hb
  obtain ⟨hk', -, hs'⟩ := convAdj κ hk
  obtain ⟨s0, hi, -⟩ := avApprox.2.1 ψ _ _ hψ
  have cc : Continuous fun t => (ψ t : ℂ) := Complex.continuous_ofReal.comp hψ.cont
  have sc : HasCompactSupport fun t => (ψ t : ℂ) := s0.comp_left Complex.ofReal_zero
  have cn : Continuous fun t => (ψ (-t) : ℂ) := cc.comp continuous_neg
  have z : ∀ t, 1 / 2 < |t| → ψ t = 0 := fun t ht => hψ.supp t fun h => by
    have : |t| ≤ 1 / 2 := abs_le.2 ⟨by linarith [h.1], h.2.trans (by norm_num)⟩
    linarith
  have n1 : ∫ x, ‖(ψ x : ℂ)‖ = 1 := by
    simp only [Complex.norm_real, Real.norm_of_nonneg (hψ.nonneg _)]; exact hψ.total
  have n2 : ∫ x, ‖(ψ (-x) : ℂ)‖ = 1 := (integral_neg_eq_self (fun x => ‖(ψ x : ℂ)‖) _).trans n1
  have n3 : ∫ x, (ψ x : ℂ) = 1 := by rw [integral_complex_ofReal, hψ.total]; simp
  have K0 : 0 ≤ K := by simpa using (norm_nonneg _).trans (hb 0 (by simp))
  have Q0 : 0 ≤ K / √3 := by positivity
  have w1 := planch κ K hk fun y => by simpa using hb (1 + y * Complex.I) (by simp)
  have w2 := planch (sharp κ) K hk' fun y => by
    rw [hs', LinearIsometryEquiv.norm_map]
    simpa using hb (-conj (1 + y * Complex.I)) (by simp)
  obtain ⟨f1, f2⟩ := traceFar M X κ hk hX ψ δ T hψ hT htc
  set e := stdOrthonormalBasis ℂ V
  set f := stdOrthonormalBasis ℂ W
  set c : _ → ℝ → ℂ := fun i => M.cor (fun x => (ψ x : ℂ)) (e i) (kv κ (e i)) with hc
  set d : _ → ℝ → ℂ := fun j => M.swap.cor (fun x => (ψ (-x) : ℂ)) (f j) (kv (sharp κ) (f j)) with hd
  have c0 : ∀ i, Continuous (c i) := fun i => continuous_const.inner (M.F.cont _)
  have d0 : ∀ j, Continuous (d j) := fun j => continuous_const.inner (M.swap.F.cont _)
  have sub : ∀ {ι : Type} [Fintype ι] (g : ι → ℝ → ℂ), (∀ i, Continuous (g i)) → ∀ a b : ℝ,
      ∫ y in a..b, ∑ i, g i (2 * y) = (1 / 2 : ℂ) * ∑ i, ∫ s in (2 * a)..(2 * b), g i s := by
    intro ι _ g hg a b
    rw [intervalIntegral.integral_finset_sum fun i _ =>
      (show Continuous fun y => g i (2 * y) from (hg i).comp (continuous_const.mul continuous_id)).intervalIntegrable _ _, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_comp_mul_left _ two_ne_zero]
    simp
  set B : ℝ := 6 / 5 * Real.exp (2 * M.T₀) * (K / √3) * Real.exp (-(2 * T)) with hB
  have tc : ∀ i β, 2 * T ≤ β → ‖∫ s in (2 * T)..β, c i s‖ ≤ B := fun i β hβ => by
    have := tailB M _ (e i) _ _ _ β cc (fun x hx => by rw [z x hx]; simp) n1.le (mul_nonneg Q0 (norm_nonneg _)) (w1 (e i)) hβ
    simpa [e.orthonormal.1 i, hB] using this
  have td : ∀ j β, 2 * T ≤ β → ‖∫ s in (2 * T)..β, d j s‖ ≤ B := fun j β hβ => by
    have := tailB M.swap _ (f j) _ _ _ β cn (fun x hx => by rw [z (-x) (by rwa [abs_neg])]; simp) n2.le
      (mul_nonneg Q0 (norm_nonneg _)) (w2 (f j)) hβ
    simp only [f.orthonormal.1 j, mul_one] at this
    exact this
  have lim : ∀ i, Tendsto (fun a : ℝ => ∫ s in (2 * T - 2 * a)..(2 * T + 2 * a), c i s) atTop (𝓝 ⟪e i, N (symb κ 0 (e i))⟫_ℂ) := fun i => by
    obtain ⟨-, k1, k2⟩ := (kvSpec κ hk).1 (e i)
    have := (corLim M _ hN _ (e i) _ (2 * T) cc sc k1).2
    rw [n3, map_one, one_mul, k2] at this
    exact this.comp (tendsto_id.const_mul_atTop two_pos)
  have tot := f2.add ((tendsto_finset_sum Finset.univ fun i _ => lim i).const_mul (1 / 2 : ℂ))
  rw [zero_add] at tot
  rw [LinearMap.trace_eq_sum_inner _ e]
  refine le_of_tendsto ((tendsto_const_nhds.sub tot).norm) ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
  have id1 := traceId M X κ hk hX ψ δ T a hψ hT ha f1
  rw [(bandTC M X κ hk hX ψ δ T (T + a) hψ (by linarith)).2.2.2.2, (bandTC M X κ hk hX ψ δ (T - a) T hψ (by linarith)).2.2.2.1,
    sub c c0, sub d d0] at id1
  have sp : ∀ i, ∫ s in (2 * T - 2 * a)..(2 * T + 2 * a), c i s =
      (∫ s in (2 * (T - a))..(2 * T), c i s) + ∫ s in (2 * T)..(2 * T + 2 * a), c i s := fun i => by
    rw [intervalIntegral.integral_add_adjacent_intervals ((c0 i).intervalIntegrable _ _) ((c0 i).intervalIntegrable _ _), mul_sub]
  simp only [sp, Finset.sum_add_distrib]
  rw [eq_sub_of_add_eq id1]
  have hd' : Module.finrank ℂ W = Module.finrank ℂ V := N.toLinearEquiv.finrank_eq
  have b1 : ‖∑ i, ∫ s in (2 * T)..(2 * T + 2 * a), c i s‖ ≤ Module.finrank ℂ V * B := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ B fun i _ => tc i _ (by linarith)).trans_eq ?_)
    simp
  have b2 : ‖∑ j, ∫ s in (2 * T)..(2 * (T + a)), d j s‖ ≤ Module.finrank ℂ V * B := by
    rw [← hd']
    refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ B fun j _ => td j _ (by linarith)).trans_eq ?_)
    simp
  have alg : ∀ R x y w : ℂ, R + 1 / 2 * x - conj (1 / 2 * w) - (R + 1 / 2 * (x + y)) = -(conj (1 / 2 * w) + 1 / 2 * y) := by
    intros; ring
  rw [alg, norm_neg]
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_conj, norm_mul, norm_mul]
  have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  have h3 : 6 / 5 * (K / √3) ≤ K := by
    have : (6 / 5 : ℝ) ≤ √3 := Real.le_sqrt_of_sq_le (by norm_num)
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  have h4 : B ≤ Real.exp (2 * M.T₀) * K * Real.exp (-2 * T) := by
    rw [hB, neg_mul, show 6 / 5 * Real.exp (2 * M.T₀) * (K / √3) = Real.exp (2 * M.T₀) * (6 / 5 * (K / √3)) by ring]
    gcongr
  have h5 : (Module.finrank ℂ V : ℝ) * B ≤ Module.finrank ℂ V * (Real.exp (2 * M.T₀) * K * Real.exp (-2 * T)) := by gcongr
  rw [h2]
  linarith
