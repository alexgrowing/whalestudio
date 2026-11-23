import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.TruncEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvDense
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CptNull
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ShNull
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CutLim
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.AvSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvSpec

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.ontoJ :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (D : Datum H V W), Function.Surjective D.J := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ D
  set J := D.J.toContinuousLinearMap with hJ
  set J' := D.J'.toContinuousLinearMap with hJ'
  set A := ContinuousLinearMap.adjoint J with hA
  set A' := ContinuousLinearMap.adjoint J' with hA'
  have aJ : ∀ u, A (D.J u) = u := fun u => ext_inner_left ℂ fun y => by
    rw [hA, ContinuousLinearMap.adjoint_inner_right]; exact D.J.inner_map_map _ _
  have aJ' : ∀ u, A' (D.J' u) = u := fun u => ext_inner_left ℂ fun y => by
    rw [hA', ContinuousLinearMap.adjoint_inner_right]; exact D.J'.inner_map_map _ _
  have iA : ∀ u h, ⟪D.J u, h⟫_ℂ = ⟪u, A h⟫_ℂ := fun u h => (ContinuousLinearMap.adjoint_inner_right J u h).symm
  have iA' : ∀ u h, ⟪D.J' u, h⟫_ℂ = ⟪u, A' h⟫_ℂ := fun u h => (ContinuousLinearMap.adjoint_inner_right J' u h).symm
  have shf : ∀ t u v, ⟪D.J (sh V t u), D.J' v⟫_ℂ = ⟪D.J u, D.J' (sh W t v)⟫_ℂ := fun t u v =>
    D.shift t u _ v _ (sh_ae V _ u) (sh_ae W _ v)
  have adV : ∀ t (x y : L V), ⟪sh V t x, y⟫_ℂ = ⟪x, sh V (-t) y⟫_ℂ := fun t x y => by
    have := (avSpec (shF V)).1 t
    rw [← ContinuousLinearMap.adjoint_inner_right]; exact congrArg (fun Z : L V →L[ℂ] L V => ⟪x, Z y⟫_ℂ) this
  have adW : ∀ t (x y : L W), ⟪sh W t x, y⟫_ℂ = ⟪x, sh W (-t) y⟫_ℂ := fun t x y => by
    have := (avSpec (shF W)).1 t
    rw [← ContinuousLinearMap.adjoint_inner_right]; exact congrArg (fun Z : L W →L[ℂ] L W => ⟪x, Z y⟫_ℂ) this
  have S1 : ∀ t v, A (D.J' (sh W t v)) = sh V (-t) (A (D.J' v)) := fun t v => ext_inner_left ℂ fun y => by
    rw [← iA, ← shf, iA, adV]
  have S2 : ∀ t u, A' (D.J (sh V (-t) u)) = sh W t (A' (D.J u)) := fun t u => ext_inner_left ℂ fun y => by
    rw [← iA', ← inner_conj_symm, shf, inner_conj_symm, iA', adW, neg_neg]
  let Q : H →L[ℂ] H := 1 - J ∘L A
  have Qa : ∀ h, Q h = h - D.J (A h) := fun _ => rfl
  have AQ : ∀ h, A (Q h) = 0 := fun h => by rw [Qa, map_sub, aJ, sub_self]
  have nQ : ∀ h, ‖Q h‖ ^ 2 = ‖h‖ ^ 2 - ‖A h‖ ^ 2 := fun h => by
    have h1 : ⟪D.J (A h), Q h⟫_ℂ = 0 := by rw [iA, AQ, inner_zero_right]
    have h2 := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h1
    rw [Qa h, add_sub_cancel, D.J.norm_map, ← Qa] at h2
    nlinarith
  let x : L W → ℝ → H := fun v t => Q (D.J' (sh W t v))
  have Ax : ∀ v t, A (x v t) = 0 := fun v t => AQ _
  have nx : ∀ v t, ‖x v t‖ = ‖Q (D.J' v)‖ := fun v t => by
    refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    rw [nQ, nQ, S1, D.J'.norm_map, D.J'.norm_map]
    exact congrArg₂ (fun a b : ℝ => a ^ 2 - b ^ 2) ((shF W).norm t v) ((shF V).norm _ _)
  have A'x : ∀ v t, A' (x v t) = sh W t (v - A' (D.J (A (D.J' v)))) := fun v t => by
    show A' (Q _) = _
    rw [Qa, map_sub, aJ', S1, S2, map_sub]
  have dense : ∀ (y : H) (ε : ℝ), 0 < ε → ∃ u v, ‖y - (D.J u + D.J' v)‖ < ε := by
    intro y ε hε
    have : (LinearMap.range D.J.toLinearMap ⊔ LinearMap.range D.J'.toLinearMap).topologicalClosure = ⊤ := by
      rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
      exact fun h hh => D.span h (fun u => hh _ (Submodule.mem_sup_left ⟨u, rfl⟩)) fun v => hh _ (Submodule.mem_sup_right ⟨v, rfl⟩)
    have hy : y ∈ closure ((LinearMap.range D.J.toLinearMap ⊔ LinearMap.range D.J'.toLinearMap : Submodule ℂ H) : Set H) := by
      rw [← Submodule.topologicalClosure_coe, this]; trivial
    obtain ⟨z, hz, hd⟩ := Metric.mem_closure_iff.1 hy ε hε
    obtain ⟨_, ⟨u, rfl⟩, _, ⟨v, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hz
    exact ⟨u, v, by rwa [dist_eq_norm] at hd⟩
  have weak : ∀ v y, Tendsto (fun t => ⟪y, x v t⟫_ℂ) atTop (𝓝 0) := by
    intro v y
    rw [Metric.tendsto_nhds]
    intro ε hε
    set c := ‖Q (D.J' v)‖ + 1 with hc
    have c0 : 0 < c := by positivity
    obtain ⟨u, w, hd⟩ := dense y (ε / 2 / c) (by positivity)
    have h1 := Metric.tendsto_nhds.1 (shNull (V := W) (v - A' (D.J (A (D.J' v)))) w).1 (ε / 2) (by positivity)
    filter_upwards [h1] with t ht
    rw [dist_zero_right] at ht ⊢
    have e : ⟪y, x v t⟫_ℂ = ⟪y - (D.J u + D.J' w), x v t⟫_ℂ + ⟪w, (shF W).U t (v - A' (D.J (A (D.J' v))))⟫_ℂ := by
      rw [inner_sub_left, inner_add_left, iA, iA', A'x, Ax, inner_zero_right, zero_add]
      exact (sub_add_cancel _ _).symm
    rw [e]
    have h2 : ‖⟪y - (D.J u + D.J' w), x v t⟫_ℂ‖ ≤ ε / 2 / c * c := by
      refine (norm_inner_le_norm _ _).trans ?_
      rw [nx]; gcongr; linarith
    rw [div_mul_cancel₀ _ c0.ne'] at h2
    linarith [norm_add_le ⟪y - (D.J u + D.J' w), x v t⟫_ℂ ⟪w, (shF W).U t (v - A' (D.J (A (D.J' v))))⟫_ℂ]
  have sup : ∀ {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X] [CompleteSpace X] (s : ℝ) (u : L X),
      ∀ᵐ x : ℝ, x ≤ s → cut X (Ioi s) u x = 0 := fun s u =>
    (((cutLaws (Ioi s) (Ioi s) measurableSet_Ioi measurableSet_Ioi).2.2.2.2.2.2.2.1 _).1
      (by simpa using DFunLike.congr_fun (cutLaws (Ioi s) (Ioi s) measurableSet_Ioi measurableSet_Ioi).1 u)).mono
      fun x h hx => h (by simpa using hx)
  set Λ : H →L[ℂ] H := 1 - J ∘L cut V (Ioi D.T₀) ∘L A - J' ∘L cut W (Ioi D.T₀) ∘L A' with hΛ
  have tr : IsTrunc D.J D.J' D.T₀ Λ := (truncEq D.J D.J' D.T₀ Λ fun u v =>
    D.causal D.T₀ _ _ (sup _ u) ((sup _ v).mono fun x h hx => h (by linarith))).2 rfl
  have Λx : ∀ v, Tendsto (fun t => x v t - Λ (x v t)) atTop (𝓝 0) := fun v => by
    have := (D.J'.continuous.tendsto 0).comp ((cutLim (v - A' (D.J (A (D.J' v))))).1 D.T₀)
    rw [map_zero] at this
    refine this.congr fun t => ?_
    show _ = x v t - (x v t - D.J (cut V _ (A (x v t))) - D.J' (cut W _ (A' (x v t))))
    rw [A'x, Ax]; simp
  have BJ : ∀ u, D.B (D.J u) = D.J (conv D.β u) := fun u => D.B_J u _ (convSpec _ D.β_ker u).1
  have BJ' : ∀ u, D.B (D.J' u) = D.J' (conv D.β' u) := fun u => D.B_J' u _ (convSpec _ D.β'_ker u).1
  have BQ : ∀ h, D.B (Q h) = Q (D.B h) := fun h => by
    have h1 : A (D.B (Q h)) = 0 := ext_inner_left ℂ fun y => by
      rw [← iA, ← D.B_sa.isSymmetric.apply_clm, BJ, iA, AQ, inner_zero_right, inner_zero_right]
    have h2 : D.B h = D.B (Q h) + D.J (conv D.β (A h)) := by rw [← BJ, ← map_add, Qa, sub_add_cancel]
    rw [Qa (D.B h)]
    conv_rhs => rw [h2, map_add, h1, aJ, zero_add, add_sub_cancel_right]
  have Bx : ∀ v t, D.B (x v t) = x (conv D.β' v) t := fun v t => by
    show D.B (Q _) = Q _
    rw [BQ, BJ']
    exact congrArg (fun z => Q (D.J' z)) (DFunLike.congr_fun ((convLaws _ D.β'_ker).1 t) v)
  have zero : ∀ v, Q (D.J' (conv D.β' v)) = 0 := fun v => by
    have t1 := cptNull atTop _ (x v) _ (D.compact _ Λ le_rfl tr) (fun t => (nx v t).le) (weak v)
    have t2 := ((Λ ∘L D.B).continuous.tendsto 0).comp (Λx v)
    have t3 := (t1.add t2).add (Λx (conv D.β' v))
    simp only [map_zero, add_zero] at t3
    have t4 : Tendsto (fun t => x (conv D.β' v) t) atTop (𝓝 0) := t3.congr fun t => by
      simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, map_sub, Bx]; abel
    have t5 := tendsto_zero_iff_norm_tendsto_zero.1 t4
    simp only [nx] at t5
    exact norm_eq_zero.1 (tendsto_nhds_unique tendsto_const_nhds t5)
  have QJ' : ∀ v, Q (D.J' v) = 0 := fun v =>
    (convDense _ D.β'_ker D.β'_unit).induction_on v (isClosed_eq (Q.continuous.comp D.J'.continuous) continuous_const) zero
  intro h
  refine ⟨A h, (sub_eq_zero.1 (D.span (Q h) (fun u => by rw [iA, AQ, inner_zero_right]) fun v => ?_)).symm⟩
  have e : D.J' v = D.J (A (D.J' v)) := sub_eq_zero.1 (QJ' v)
  rw [e, iA, AQ, inner_zero_right]
