import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.ExpForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.ActLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.ActUniq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.PosSymb

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

section SlopeTestRemainingChoices

variable {H V W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W]

omit [FiniteDimensional ℂ V] [CompleteSpace V] [FiniteDimensional ℂ W] [CompleteSpace W] in
private theorem lift_sh (S : V →L[ℂ] W) (S' : W →L[ℂ] V) (c : V →L[ℂ] V) (t : ℝ) (x : L W) :
    (S ∘L c ∘L S').compLpL 2 volume (sh W t x) =
      S.compLpL 2 volume (c.compLpL 2 volume (sh V t (S'.compLpL 2 volume x))) := by
  refine Lp.ext ?_
  filter_upwards [(S ∘L c ∘L S').coeFn_compLpL (sh W t x), sh_ae W t x,
    S.coeFn_compLpL (c.compLpL 2 volume (sh V t (S'.compLpL 2 volume x))),
    c.coeFn_compLpL (sh V t (S'.compLpL 2 volume x)), sh_ae V t (S'.compLpL 2 volume x),
    (measurePreserving_add_right volume t).quasiMeasurePreserving.ae (S'.coeFn_compLpL x)] with y h1 h2 h3 h4 h5 h6
  rw [h1, h2, h3, h4, h5, h6]; rfl

private theorem act_transp (J : L V →ₗᵢ[ℂ] H) (J' : L W →ₗᵢ[ℂ] H) (S : V →L[ℂ] W) (S' : W →L[ℂ] V) (T T' Y : H →L[ℂ] H)
    (hT : ∀ u, T (J u) = J' (S.compLpL 2 volume u)) (hT' : ∀ w, T' (J' w) = J (S'.compLpL 2 volume w))
    (σ : ℂ → V →L[ℂ] V) (h : Act J Y σ) : Act J' (T ∘L Y ∘L T') fun z => S ∘L σ z ∘L S' := by
  obtain ⟨u, κ, hk, h1, h2⟩ := h
  have hk' : Ker fun t => S ∘L κ t ∘L S' := by
    refine ⟨continuous_const.clm_comp (hk.1.clm_comp continuous_const), hk.2.mono fun t ht h0 => ht ?_⟩
    simp [h0]
  refine ⟨u.mapRange (fun c => S ∘L c ∘L S') (by simp), fun t => S ∘L κ t ∘L S', hk', fun x => ?_, fun z => ?_⟩
  · rw [Finsupp.sum_mapRange_index fun a => Lp.ext (by
      filter_upwards [(0 : W →L[ℂ] W).coeFn_compLpL (sh W a x), Lp.coeFn_zero W 2 (volume : Measure ℝ)] with y a b
      rw [a, b]; rfl)]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hT', h1, hT, map_add, Finsupp.sum, Finsupp.sum, map_sum, (convSpec _ hk' x).2.2, (convSpec _ hk _).2.2,
      ← ContinuousLinearMap.integral_comp_comm _ (convSpec _ hk _).2.1]
    simp only [lift_sh]
  · beta_reduce
    rw [Finsupp.sum_mapRange_index (by simp), h2]
    have hi : Integrable fun t : ℝ => Complex.exp (z * t) • κ t := by
      have c0 : Continuous fun t : ℝ => Complex.exp (z * t) := by fun_prop
      refine Continuous.integrable_of_hasCompactSupport (c0.smul hk.1) (hk.2.mono fun t ht h0 => ht ?_)
      show Complex.exp (z * t) • κ t = 0
      rw [h0, smul_zero]
    let Φ : (V →L[ℂ] V) →L[ℂ] (W →L[ℂ] W) :=
      (ContinuousLinearMap.compL ℂ W V W S) ∘L ((ContinuousLinearMap.compL ℂ W V V).flip S')
    have hΦ : ∀ c, Φ c = S ∘L c ∘L S' := fun c => rfl
    simp only [← hΦ, symb, Finsupp.sum, map_add, map_sum, map_smul]
    rw [← Φ.integral_comp_comm hi]
    simp only [map_smul]

omit [FiniteDimensional ℂ V] [CompleteSpace V] [CompleteSpace H] in
private theorem act_congr (J : L V →ₗᵢ[ℂ] H) (Y Y' : H →L[ℂ] H) (σ : ℂ → V →L[ℂ] V) (e : ∀ u, Y' (J u) = Y (J u))
    (h : Act J Y σ) : Act J Y' σ := by
  obtain ⟨u, κ, hk, h1, h2⟩ := h
  exact ⟨u, κ, hk, fun x => (e x).trans (h1 x), h2⟩

private theorem act_comm (J : L V →ₗᵢ[ℂ] H) (Y Y' : H →L[ℂ] H) (σ σ' : ℂ → V →L[ℂ] V) (e : Commute Y Y')
    (h : Act J Y σ) (h' : Act J Y' σ') : Commute (σ 0) (σ' 0) := by
  have a := ((actLaws J).2.2.2.1 _ _ _ _ h h').2
  have b := ((actLaws J).2.2.2.1 _ _ _ _ h' h).2
  have e' : Y ∘L Y' = Y' ∘L Y := e
  rw [e'] at a
  exact congrFun (actUniq J _ _ _ a b) 0

private theorem eigP_comm {d : ℕ} (a u : Eu d →L[ℂ] Eu d) (ha : IsSelfAdjoint a) (h : Commute u a) (x : ℝ) :
    Commute (eigP a x) u := by
  have key : ∀ w : Eu d →L[ℂ] Eu d, Commute w a → ∀ v ∈ Module.End.eigenspace (a : Eu d →ₗ[ℂ] Eu d) (x : ℂ),
      w v ∈ Module.End.eigenspace (a : Eu d →ₗ[ℂ] Eu d) (x : ℂ) := by
    intro w hw v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    have h1 : w (a v) = a (w v) := DFunLike.congr_fun hw.eq v
    have h2 : a v = (x : ℂ) • v := hv
    show a (w v) = _
    rw [← h1, h2, map_smul]
  have h' : Commute (star u) a := by
    have := h.star_star
    rwa [ha.star_eq] at this
  refine ContinuousLinearMap.ext fun v => ?_
  show eigP a x (u v) = u (eigP a x v)
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (key u h _ (Submodule.starProjection_apply_mem _ v)) fun w hw => ?_
  rw [← map_sub, ← ContinuousLinearMap.adjoint_inner_right]
  exact Submodule.starProjection_inner_eq_zero v _ (key _ h' w hw)

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.famExp :
    ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {μ : Measure (normOneGL E (2 + 2))} [μ.IsHaarMeasure] {θ : Twist μ} {𝔢 : Side θ 2} (𝔵 : Fam 𝔢) (N : Eu 𝔵.d' ≃ₗᵢ[ℂ] Eu 𝔵.d) (C₀ : ℝ), Family2 μ 𝔵.A 𝔵.A' 𝔵.P N C₀ → 0 ≤ 𝔢.toAmp.A → ‖𝔢.toAmp.A‖ ≤ 1 →
      (∃ sp : Finset ℝ, (∀ x, x ∈ sp ↔ 0 < x ∧ Module.End.eigenspace (𝔵.a₀ : Eu 𝔵.d' →ₗ[ℂ] Eu 𝔵.d') (x : ℂ) ≠ ⊥) ∧ (∀ x ∈ sp, x ≤ 1) ∧
        ∀ x : ℝ, 0 < x → x ∉ sp → ∀ j, 𝔵.tr N x j = 0) ∧
      ∀ x : ℝ, ∃ (s : Finset ℂ) (c : ℂ → ℂ), 0 ∉ s ∧ ∀ᶠ j : ℕ in atTop, 𝔵.tr N x j = ∑ ζ ∈ s, c ζ * ζ ^ j := by
  intro E _ _ _ μ _ θ 𝔢 𝔵 N C₀ hF h0 h1
  have ha : Conv 𝔵.A'.J 𝔵.A'.J 𝔢.toAmp.A 𝔵.βa := 𝔢.a_op ▸ 𝔵.a_acts.2.1
  obtain ⟨p0, p1⟩ : 0 ≤ 𝔵.a₀ ∧ ‖𝔵.a₀‖ ≤ 1 := posSymb 𝔵.A'.J _ _ 𝔵.a_acts.1 ha h0 h1
  refine ⟨?_, fun x => ?_⟩
  · have fin : {x : ℝ | 0 < x ∧ Module.End.eigenspace (𝔵.a₀ : Eu 𝔵.d' →ₗ[ℂ] Eu 𝔵.d') (x : ℂ) ≠ ⊥}.Finite :=
      ((Module.End.finite_hasEigenvalue (𝔵.a₀ : Eu 𝔵.d' →ₗ[ℂ] Eu 𝔵.d')).preimage
        Complex.ofReal_injective.injOn).subset fun x hx => hx.2
    refine ⟨fin.toFinset, fun x => fin.mem_toFinset, fun x hx => ?_, fun x hx hx' j => ?_⟩
    · obtain ⟨hx0, hx⟩ := fin.mem_toFinset.1 hx
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hx
      have e : 𝔵.a₀ v = (x : ℂ) • v := Module.End.mem_eigenspace_iff.1 hv
      have := (𝔵.a₀.le_opNorm v).trans (mul_le_mul_of_nonneg_right p1 (norm_nonneg v))
      rw [e, norm_smul, Complex.norm_real, Real.norm_of_nonneg hx0.le] at this
      exact le_of_mul_le_mul_right this (norm_pos_iff.2 hv0)
    · have hb : Module.End.eigenspace (𝔵.a₀ : Eu 𝔵.d' →ₗ[ℂ] Eu 𝔵.d') (x : ℂ) = ⊥ := by
        by_contra hb
        exact hx' (fin.mem_toFinset.2 ⟨hx, hb⟩)
      have : eigP 𝔵.a₀ x = 0 := by
        refine ContinuousLinearMap.ext fun v => ?_
        have := Submodule.starProjection_apply_mem (Module.End.eigenspace (𝔵.a₀ : Eu 𝔵.d' →ₗ[ℂ] Eu 𝔵.d') (x : ℂ)) v
        exact (Submodule.eq_bot_iff _).1 hb _ this
      simp [Fam.tr, this]
  · have sa : IsSelfAdjoint 𝔵.a₀ := IsSelfAdjoint.of_nonneg p0
    have aA : Act 𝔵.A'.J 𝔢.toAmp.A (symb 𝔵.βa) := (actLaws _).2.1 _ _ 𝔵.a_acts.1 ha
    have aG : Act 𝔵.A'.J (Rop μ 𝔢.g) (symb 𝔵.βg) := (actLaws _).2.1 _ _ 𝔵.g_acts.1 𝔵.g_acts.2.1
    have cP : ∀ i, Commute (eigP 𝔵.a₀ x) (𝔵.u i 0) := fun i =>
      eigP_comm _ _ sa (act_comm _ _ _ _ _ (𝔢.Uq_amp i) (𝔵.u_act i) aA) x
    let S : Eu 𝔵.d →L[ℂ] Eu 𝔵.d' := 𝔵.s.toContinuousLinearEquiv
    let S' : Eu 𝔵.d' →L[ℂ] Eu 𝔵.d := 𝔵.s.symm.toContinuousLinearEquiv
    let T' : L2 μ →L[ℂ] L2 μ :=
      𝔵.A.J.toContinuousLinearMap ∘L S'.compLpL 2 volume ∘L ContinuousLinearMap.adjoint 𝔵.A'.J.toContinuousLinearMap
    have hT : ∀ u, θ.U (𝔵.A.J u) = 𝔵.A'.J (S.compLpL 2 volume u) := fun u => 𝔵.s_op u _ (S.coeFn_compLpL u)
    have hT' : ∀ w, T' (𝔵.A'.J w) = 𝔵.A.J (S'.compLpL 2 volume w) := fun w => by
      have : ContinuousLinearMap.adjoint 𝔵.A'.J.toContinuousLinearMap (𝔵.A'.J w) = w := by
        refine ext_inner_left ℂ fun y => ?_
        rw [ContinuousLinearMap.adjoint_inner_right]
        exact 𝔵.A'.J.inner_map_map y w
      show 𝔵.A.J (S'.compLpL 2 volume (ContinuousLinearMap.adjoint 𝔵.A'.J.toContinuousLinearMap (𝔵.A'.J w))) = _
      rw [this]
    have hTT : ∀ w, θ.U (T' (𝔵.A'.J w)) = 𝔵.A'.J w := fun w => by
      rw [hT']
      refine 𝔵.s_op _ _ ?_
      filter_upwards [S'.coeFn_compLpL w] with y hy
      rw [hy]
      exact (𝔵.s.apply_symm_apply _).symm
    have perm : ∀ i w, symb 𝔵.βg 0 (𝔵.s (𝔵.v i 0 w)) = 𝔵.u (i + 1) 0 (symb 𝔵.βg 0 (𝔵.s w)) := fun i w => by
      have a := ((actLaws _).2.2.2.1 _ _ _ _ aG (act_transp _ _ S S' _ _ _ hT hT' _ (𝔵.v_act i))).2
      have b := ((actLaws _).2.2.2.1 _ _ _ _ (𝔵.u_act (i + 1)) aG).2
      have c := actUniq _ _ _ _ a (act_congr _ _ _ _ (fun y => ?_) b)
      · have := DFunLike.congr_fun (congrFun c 0) (𝔵.s w)
        simpa [S, S'] using this
      · have := DFunLike.congr_fun (𝔢.Uq_perm i) (T' (𝔵.A'.J y))
        simp only [ContinuousLinearMap.comp_apply] at this ⊢
        rw [this, hTT]
    let B : Module.End ℂ (Eu 𝔵.d') := ((eigP 𝔵.a₀ x ∘L symb 𝔵.βg 0 : Eu 𝔵.d' →L[ℂ] Eu 𝔵.d') : Eu 𝔵.d' →ₗ[ℂ] Eu 𝔵.d') ∘ₗ
      (𝔵.s.toLinearEquiv : Eu 𝔵.d →ₗ[ℂ] Eu 𝔵.d') ∘ₗ (N.toLinearEquiv : Eu 𝔵.d' →ₗ[ℂ] Eu 𝔵.d)
    have hB : ∀ w, B w = eigP 𝔵.a₀ x (symb 𝔵.βg 0 (𝔵.s (N w))) := fun w => rfl
    obtain ⟨s, c, hs, h⟩ := expForm (Eu 𝔵.d') 2 two_pos (fun i => (𝔵.u i 0 : Eu 𝔵.d' →ₗ[ℂ] Eu 𝔵.d')) B
      (fun i k => LinearMap.ext fun w =>
        DFunLike.congr_fun (act_comm _ _ _ _ _ (𝔢.Uq_comm i k) (𝔵.u_act i) (𝔵.u_act k)).eq w)
      (fun i => LinearMap.ext fun w => by
        show B (𝔵.u i 0 w) = 𝔵.u (i + 1) 0 (B w)
        rw [hB, hB, hF.2 _ _ _ (𝔵.v_act i) (𝔵.u_act i), perm]
        exact DFunLike.congr_fun (cP (i + 1)).eq _)
    refine ⟨s, c, hs, (eventually_ge_atTop (Module.finrank ℂ (Eu 𝔵.d'))).mono fun j hj => ?_⟩
    rw [← h j hj, Fam.tr, LinearMap.trace_comp_comm']
    congr 1
    refine LinearMap.ext fun w => ?_
    have e : ((𝔵.u 0 0 ^ j : Eu 𝔵.d' →L[ℂ] Eu 𝔵.d') : Eu 𝔵.d' →ₗ[ℂ] Eu 𝔵.d') = (𝔵.u 0 0 : Eu 𝔵.d' →ₗ[ℂ] Eu 𝔵.d') ^ j :=
      map_pow (ContinuousLinearMap.toLinearMapRingHom (R₁ := ℂ) (M₁ := Eu 𝔵.d')) _ j
    rw [Module.End.mul_apply, hB, ← e]
    exact DFunLike.congr_fun ((cP 0).pow_right j).eq _
