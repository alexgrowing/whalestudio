import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.BandHS
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.TrWeak
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CarLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ProjLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.AvSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.AvApprox
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvAdj

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W)

private theorem k1 {T : ℝ} (hT : M.T₀ ≤ T) {r : ℝ} (hr : r ≤ 0) (h : H) : M.abelian₂ T T (M.F.U r (M.P (Ioi T) h)) = 0 := by
  obtain ⟨-, -, -, -, hP, -, -, hL⟩ := projLaws M
  have x1 := DFunLike.congr_fun ((hP _ _ (measurableSet_Ioi (a := T)) (measurableSet_Ioi (a := T))).2.2.2.2 r).1 h
  have y1 : (fun x : ℝ => x + r) ⁻¹' Ioi T = Ioi (T - r) := by ext x; simp [sub_lt_iff_lt_add]
  have x2 := (hP _ _ (measurableSet_Ioi (a := T)) (measurableSet_Ioi (a := T - r))).1
  rw [inter_eq_right.2 (Ioi_subset_Ioi (by linarith))] at x2
  rw [y1, ← x2] at x1
  simp only [ContinuousLinearMap.comp_apply] at x1
  rw [x1]
  exact DFunLike.congr_fun (hL T T (by linarith)).2.2.2.2.2.1 _

private theorem k2 {T δ : ℝ} (hT : M.T₀ ≤ T) {r : ℝ} (hr : -δ ≤ r) (h : H) : M.abelian₂ T T (M.F.U r (M.P' (Ioi (T + δ)) h)) = 0 := by
  obtain ⟨-, -, -, -, hP, -, -, hL⟩ := projLaws M
  have x1 := DFunLike.congr_fun ((hP _ _ (measurableSet_Ioi (a := T + δ)) (measurableSet_Ioi (a := T))).2.2.2.2 r).2 h
  have y1 : (fun x : ℝ => x - r) ⁻¹' Ioi (T + δ) = Ioi (T + δ + r) := by ext x; simp [lt_sub_iff_add_lt]
  have x2 : M.P' (Ioi T) ∘L M.P' (Ioi (T + δ + r)) = M.P' (Ioi T ∩ Ioi (T + δ + r)) :=
    ((projLaws M.swap).2.2.2.2.1 _ _ (measurableSet_Ioi (a := T)) (measurableSet_Ioi (a := T + δ + r))).1
  rw [inter_eq_right.2 (Ioi_subset_Ioi (by linarith))] at x2
  rw [y1, ← x2] at x1
  simp only [ContinuousLinearMap.comp_apply] at x1
  rw [x1]
  exact DFunLike.congr_fun (hL T T (by linarith)).2.2.2.2.2.2.2.1 _

private theorem k3 {ψ : ℝ → ℝ} {δ : ℝ} (hψ : Bump ψ (-δ) 0) (A : H →L[ℂ] H) (h : H)
    (hA : ∀ r, -δ ≤ r → r ≤ 0 → A (M.F.U r h) = 0) : A (M.F.av (fun t => (ψ t : ℂ)) h) = 0 := by
  obtain ⟨i, e⟩ := ((avSpec M.F).2.2.2 _ (avApprox.2.1 ψ _ _ hψ).2.1).1 h
  rw [e, ← A.integral_comp_comm i]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun r => ?_)
  by_cases hr : r ∈ Icc (-δ) 0
  · simp [hA r hr.1 hr.2]
  · simp [hψ.supp r hr]

private theorem k4 {T ρ : ℝ} (hρ : 0 ≤ ρ) : M.P' (Ioi T) = M.P' (Ioc T (T + ρ)) + M.P' (Ioi (T + ρ)) := by
  have := ((projLaws M.swap).2.2.2.2.1 _ _ (measurableSet_Ioc (a := T) (b := T + ρ)) (measurableSet_Ioi (a := T + ρ))).2.2.2.1
    (Ioc_disjoint_Ioi le_rfl)
  rwa [Ioc_union_Ioi_eq_Ioi (by linarith)] at this

private theorem k5 (T : ℝ) (h : H) : h = M.abelian₂ T T h + M.P (Ioi T) h + M.P' (Ioi T) h := by
  show h = h - M.P (Ioi T) h - M.P' (Ioi T) h + _ + _
  abel

private theorem k6 {X : H →L[ℂ] H} {κ : ℝ → V →L[ℂ] W} (hk : Ker κ) (hX : M.Carries X κ) {ψ : ℝ → ℝ} {δ : ℝ} (hψ : Bump ψ (-δ) 0)
    {a b : ℝ} (hab : a ≤ b) :
    IsHilbertSchmidt (M.F.av (fun t => (ψ t : ℂ)) ∘L M.P' (Ioc a b)) ∧ IsHilbertSchmidt (M.P' (Ioc a b) ∘L X) ∧
    hsNorm (M.F.av (fun t => (ψ t : ℂ)) ∘L M.P' (Ioc a b)) ^ 2 = (b - a) * (Module.finrank ℂ W * ∫ x, ψ x ^ 2) ∧
    hsNorm (M.P' (Ioc a b) ∘L X) ^ 2 = (b - a) * ∑ i, ‖kv (sharp κ) (stdOrthonormalBasis ℂ W i)‖ ^ 2 ∧
    M.P' (Ioc a b) ∘L M.P' (Ioc a b) = M.P' (Ioc a b) := by
  obtain ⟨hs, hi, -⟩ := avApprox.2.1 ψ _ _ hψ
  obtain ⟨b1, b2, b3, b4, -⟩ := bandHS M.swap _ _ (convAdj κ hk).1 (carLaws M X κ hk hX).2.1 (fun t => (ψ (-t) : ℂ)) a b
    (Complex.continuous_ofReal.comp (hψ.cont.comp continuous_neg))
    ((hs.comp_homeomorph (Homeomorph.neg ℝ)).comp_left (g := fun x : ℝ => (x : ℂ)) rfl) hab
  have e : M.swap.F.av (fun t => (ψ (-t) : ℂ)) = M.F.av fun t => (ψ t : ℂ) := by
    have := ((avSpec M.F).2.2.2 _ hi.comp_neg).2.2.2.1
    simp only [neg_neg] at this
    exact this
  rw [e] at b3 b4
  obtain ⟨p1, p2, -⟩ := (projLaws M.swap).2.2.2.2.1 _ _ (measurableSet_Ioc (a := a) (b := b)) (measurableSet_Ioc (a := a) (b := b))
  rw [inter_self] at p1
  have e2 : M.P' (Ioc a b) ∘L X = ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint X ∘L M.swap.P (Ioc a b)) := by
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint, p2.adjoint_eq]; rfl
  refine ⟨b3, e2 ▸ b1.adjoint, b4.trans ?_, by rw [e2, hsNorm_adjoint, b2], p1⟩
  have := integral_neg_eq_self (fun x => ψ x ^ 2) volume
  simp [this]
end

theorem UpperTheory.V.Z.IntegralApplyAeEq.traceNear :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (X : H →L[ℂ] H) (κ : ℝ → V →L[ℂ] W), Ker κ → M.Carries X κ → ∀ T : ℝ, M.T₀ ≤ T → IsTraceClass (M.abelian₂ T T ∘L X ∘L M.abelian₂ T T) → ∀ ε : ℝ, 0 < ε →
      ∃ (ψ : ℝ → ℝ) (δ : ℝ), 0 < δ ∧ δ ≤ 1 / 2 ∧ Bump ψ (-δ) 0 ∧
        ‖trace (M.abelian₂ T T ∘L (M.F.av (fun t => (ψ t : ℂ)) ∘L X) ∘L M.abelian₂ T T) - trace (M.abelian₂ T T ∘L X ∘L M.abelian₂ T T)‖ ≤ ε := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M X κ hk hX T hT htc ε hε
  obtain ⟨-, -, l0, sa, ln, -⟩ := (projLaws M).2.2.2.2.2.2.2 T T (by linarith)
  set Λ := M.abelian₂ T T
  let d : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) / 2
  have d0 : ∀ n, 0 < d n := fun n => by positivity
  have d1 : ∀ n, d n ≤ 1 / 2 := fun n => by
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
    show _ / 2 ≤ _; linarith
  have dt : Tendsto d atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat.div_const (2 : ℝ)
    rwa [zero_div] at this
  choose ψ hψ using fun n => avApprox.1 (-d n) 0 (by linarith [d0 n])
  let Ψ : ℕ → H →L[ℂ] H := fun n => M.F.av fun t => (ψ n t : ℂ)
  have nΨ : ∀ n, ‖Ψ n‖ ≤ 1 := fun n => by
    refine ((avSpec M.F).2.2.2 _ (avApprox.2.1 _ _ _ (hψ n)).2.1).2.1.trans_eq ?_
    rw [← (hψ n).total]
    exact integral_congr_ae (Eventually.of_forall fun t => by simp [abs_of_nonneg ((hψ n).nonneg t)])
  have sΨ : ∀ h, Tendsto (fun n => Ψ n h) atTop (𝓝 h) := fun h => by
    rw [Metric.tendsto_nhds]
    intro η hη
    obtain ⟨δ, hδ, H1⟩ := avApprox.2.2 M.F h (η / 2) (by positivity)
    filter_upwards [dt.eventually (ge_mem_nhds hδ)] with n hn
    rw [dist_eq_norm]
    linarith [H1 _ _ _ (hψ n) (neg_le_neg hn) hδ.le]
  have t1 := trWeak atTop (fun n => Λ ∘L Ψ n) Λ _ htc
    (fun n => (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_one₀ ln (norm_nonneg _) (nΨ n)))
    fun x y => tendsto_const_nhds.inner ((Λ.continuous.tendsto y).comp (sΨ y))
  rw [show Λ ∘L (Λ ∘L X ∘L Λ) = Λ ∘L X ∘L Λ from congrArg (· ∘L (X ∘L Λ)) l0] at t1
  set c := ∑ i, ‖kv (sharp κ) (stdOrthonormalBasis ℂ W i)‖ ^ 2
  have t2 : Tendsto (fun n => √(2 * Module.finrank ℂ W) * √(d n * c)) atTop (𝓝 0) := by
    simpa using ((dt.mul_const c).sqrt).const_mul √(2 * Module.finrank ℂ W)
  obtain ⟨n, hn1, hn2⟩ := ((Metric.tendsto_nhds.1 t1 (ε / 2) (by positivity)).and
    (t2.eventually (ge_mem_nhds (show 0 < ε / 2 by positivity)))).exists
  refine ⟨ψ n, d n, d0 n, d1 n, hψ n, ?_⟩
  obtain ⟨h1, h2, h4, h5, h3⟩ := k6 M hk hX (hψ n) (a := T) (b := T + d n) (by linarith [d0 n])
  set E := M.P' (Ioc T (T + d n))
  have key : Λ ∘L (Ψ n ∘L X) ∘L Λ = (Λ ∘L Ψ n) ∘L (Λ ∘L X ∘L Λ) + (Λ ∘L (Ψ n ∘L E)) ∘L ((E ∘L X) ∘L Λ) := by
    ext h
    have a1 : Λ (Ψ n (M.P (Ioi T) (X (Λ h)))) = 0 := k3 M (hψ n) _ _ fun r _ hr => k1 M hT hr _
    have a2 : Λ (Ψ n (M.P' (Ioi (T + d n)) (X (Λ h)))) = 0 := k3 M (hψ n) _ _ fun r hr _ => k2 M hT hr _
    have a3 : E (E (X (Λ h))) = E (X (Λ h)) := DFunLike.congr_fun h3 _
    show Λ (Ψ n (X (Λ h))) = Λ (Ψ n (Λ (X (Λ h)))) + Λ (Ψ n (E (E (X (Λ h)))))
    conv_lhs => rw [k5 M T (X (Λ h)), k4 M (d0 n).le, ContinuousLinearMap.add_apply]
    simp only [map_add]
    rw [a1, a2, a3, add_zero, add_zero]
  have g1 := h1.comp_left Λ
  have g2 := h2.comp_right Λ
  have tc := isTraceClass_comp g1 g2
  have nl : ‖Λ‖ₑ ≤ 1 := enorm_le_one_of_norm_le_one ln
  have b1 : hsNorm (Λ ∘L (Ψ n ∘L E)) ≤ √(2 * Module.finrank ℂ W) := by
    refine Real.le_sqrt_of_sq_le ?_
    have : hsNorm (Λ ∘L (Ψ n ∘L E)) ^ 2 ≤ hsNorm (Ψ n ∘L E) ^ 2 := by
      rw [hsNorm_sq, hsNorm_sq]
      refine ENNReal.toReal_mono (ne_of_lt h1) ((hsNormSq_comp_left_le _ _).trans ?_)
      exact mul_le_of_le_one_left' (pow_le_one' nl 2)
    refine this.trans (h4.trans_le ?_)
    have i := (avApprox.2.1 _ _ _ (hψ n)).2.2
    rw [add_sub_cancel_left]
    rw [sub_neg_eq_add, zero_add, le_div_iff₀ (d0 n)] at i
    nlinarith [Nat.cast_nonneg (α := ℝ) (Module.finrank ℂ W)]
  have b2 : hsNorm ((E ∘L X) ∘L Λ) ≤ √(d n * c) := by
    refine Real.le_sqrt_of_sq_le ?_
    have : hsNorm ((E ∘L X) ∘L Λ) ^ 2 ≤ hsNorm (E ∘L X) ^ 2 := by
      rw [hsNorm_sq, hsNorm_sq]
      refine ENNReal.toReal_mono (ne_of_lt h2) ((hsNormSq_comp_right_le _ _).trans ?_)
      exact mul_le_of_le_one_left' (pow_le_one' nl 2)
    exact this.trans (h5.trans (by rw [add_sub_cancel_left])).le
  have b3 : ‖trace ((Λ ∘L (Ψ n ∘L E)) ∘L ((E ∘L X) ∘L Λ))‖ ≤ ε / 2 := by
    refine le_trans ?_ ((traceNorm_comp_le g1 g2).trans ((mul_le_mul b1 b2 (hsNorm_nonneg _) (Real.sqrt_nonneg _)).trans hn2))
    have := ENNReal.toReal_mono (ne_of_lt tc) (enorm_trace_le ((Λ ∘L (Ψ n ∘L E)) ∘L ((E ∘L X) ∘L Λ)))
    simpa using this
  show ‖trace (Λ ∘L (Ψ n ∘L X) ∘L Λ) - _‖ ≤ ε
  rw [key, trace_add (htc.comp_left _) tc, add_sub_right_comm]
  rw [dist_eq_norm] at hn1
  exact (norm_add_le _ _).trans (by linarith)
