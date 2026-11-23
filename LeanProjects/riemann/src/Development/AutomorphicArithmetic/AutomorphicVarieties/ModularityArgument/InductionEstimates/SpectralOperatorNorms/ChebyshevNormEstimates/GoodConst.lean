import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.ActLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.ActUniq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.HeckeEigenvalueRankTwoData
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.ConvBump
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.HeckeP

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

section SlopeTestRemainingChoices

variable {H V : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V]

private def Good (J : L V →ₗᵢ[ℂ] H) (P : H →L[ℂ] H) (a : V →L[ℂ] V) (Y : H →L[ℂ] H) (c : ℝ → ℂ) : Prop :=
  (∃ s, Act J Y s ∧ ∀ x : ℝ, 0 < x → ∀ v ∈ Module.End.eigenspace (a : V →ₗ[ℂ] V) (x : ℂ), s 0 v = c x • v) ∧
    Y ∘L P = P ∘L Y

variable {J : L V →ₗᵢ[ℂ] H} {P : H →L[ℂ] H} {a : V →L[ℂ] V}

private theorem act_const (c : ℂ) : Act J (c • (1 : H →L[ℂ] H)) fun _ => c • (1 : V →L[ℂ] V) :=
  ((actLaws J).2.2.1 _ _ (actLaws J).1).2 c

private theorem good_const (c : ℂ) : Good J P a (c • (1 : H →L[ℂ] H)) fun _ => c := by
  refine ⟨⟨_, act_const c, fun x _ v _ => by simp⟩, ?_⟩
  ext v
  simp

private theorem good_add {Y Y' : H →L[ℂ] H} {c c' : ℝ → ℂ} (h : Good J P a Y c) (h' : Good J P a Y' c') :
    Good J P a (Y + Y') fun x => c x + c' x := by
  obtain ⟨⟨s, hs, hz⟩, hc⟩ := h
  obtain ⟨⟨s', hs', hz'⟩, hc'⟩ := h'
  refine ⟨⟨_, ((actLaws J).2.2.2.1 _ _ _ _ hs hs').1, fun x hx v hv => ?_⟩, ?_⟩
  · simp only [ContinuousLinearMap.add_apply, hz x hx v hv, hz' x hx v hv, add_smul]
  · rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, hc, hc']

private theorem good_mul {Y Y' : H →L[ℂ] H} {c c' : ℝ → ℂ} (h : Good J P a Y c) (h' : Good J P a Y' c') :
    Good J P a (Y * Y') fun x => c x * c' x := by
  obtain ⟨⟨s, hs, hz⟩, hc⟩ := h
  obtain ⟨⟨s', hs', hz'⟩, hc'⟩ := h'
  refine ⟨⟨_, ((actLaws J).2.2.2.1 _ _ _ _ hs hs').2, fun x hx v hv => ?_⟩, ?_⟩
  · simp only [ContinuousLinearMap.comp_apply, hz x hx v hv, hz' x hx v hv, map_smul, smul_smul, mul_comm]
  · change (Y ∘L Y') ∘L P = P ∘L (Y ∘L Y')
    rw [ContinuousLinearMap.comp_assoc, hc', ← ContinuousLinearMap.comp_assoc, hc, ContinuousLinearMap.comp_assoc]

private theorem symb_hom {R : Type} [Semiring R] (f : R →+* (H →L[ℂ] H)) (h : ∀ r, ∃ s, Act J (f r) s) :
    ∃ e : ℂ → R →+* (V →L[ℂ] V), ∀ r, Act J (f r) fun z => e z r := by
  choose s hs using h
  have h1 : s 1 = fun _ => 1 := actUniq J _ _ _ (hs 1) (by rw [map_one]; exact (actLaws J).1)
  have h0 : s 0 = fun _ => 0 := actUniq J _ _ _ (hs 0) (by
    have := act_const (J := J) 0
    rw [map_zero]
    simpa only [zero_smul] using this)
  have ha : ∀ r r', s (r + r') = fun z => s r z + s r' z := fun r r' =>
    actUniq J _ _ _ (hs _) (by rw [map_add]; exact ((actLaws J).2.2.2.1 _ _ _ _ (hs r) (hs r')).1)
  have hm : ∀ r r', s (r * r') = fun z => s r z * s r' z := fun r r' =>
    actUniq J _ _ _ (hs _) (by rw [map_mul]; exact ((actLaws J).2.2.2.1 _ _ _ _ (hs r) (hs r')).2)
  exact ⟨fun z =>
    { toFun := fun r => s r z
      map_one' := congrFun h1 z
      map_mul' := fun r r' => congrFun (hm r r') z
      map_zero' := congrFun h0 z
      map_add' := fun r r' => congrFun (ha r r') z }, hs⟩

private theorem good_poly {σ τ : Type} (f : MvPolynomial σ (MvPolynomial τ ℂ) →+* (H →L[ℂ] H))
    (g : ℝ → MvPolynomial σ (MvPolynomial τ ℂ) →+* ℂ)
    (hc : ∀ c, Good J P a (f (C (C c))) fun x => g x (C (C c)))
    (ht : ∀ t, Good J P a (f (C (X t))) fun x => g x (C (X t)))
    (hs : ∀ s, Good J P a (f (X s)) fun x => g x (X s)) (r : MvPolynomial σ (MvPolynomial τ ℂ)) :
    Good J P a (f r) fun x => g x r := by
  induction r using MvPolynomial.induction_on with
  | C p =>
    induction p using MvPolynomial.induction_on with
    | C c => exact hc c
    | add p q hp hq => simpa only [map_add] using good_add hp hq
    | mul_X p t hp => simpa only [map_mul] using good_mul hp (ht t)
  | add p q hp hq => simpa only [map_add] using good_add hp hq
  | mul_X p t hp => simpa only [map_mul] using good_mul hp (hs t)

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.evzEx :
    ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {μ : Measure (normOneGL E (2 + 2))} [μ.IsHaarMeasure] {θ : Twist μ} {𝔢 : Side θ 2} (𝔵 : Fam 𝔢) (ev : PR E (2 + 2) →+* (LL μ →L[ℂ] LL μ)), 𝔢.toAmp.IsEv ev → ∃ evz, 𝔵.IsEvz ev evz := by
  intro E _ _ _ μ _ θ 𝔢 𝔵 ev hev
  classical
  let π : PR E (2 + 2) →+* PR E (2 + 2) := eval₂Hom C fun y => if y.1 ∈ 𝔢.S then 0 else X y
  have hπC : ∀ p, π (C p) = C p := fun p => eval₂Hom_C _ _ _
  have hπX : ∀ y, π (X y) = if y.1 ∈ 𝔢.S then 0 else X y := fun y => eval₂Hom_X' _ _ _
  have hπ : ∀ R : PR E (2 + 2), (∀ y ∈ R.vars, y.1 ∉ 𝔢.S) → π R = R := fun R hR =>
    hom_congr_vars (f₁ := π) (f₂ := RingHom.id _) (RingHom.ext fun p => hπC p)
      (fun y hy _ => by rw [hπX, if_neg (hR y hy)]; rfl) rfl
  have hA : Act 𝔵.A'.J 𝔢.toAmp.A (symb 𝔵.βa) := by
    rw [← 𝔢.a_op]
    exact (actLaws 𝔵.A'.J).2.1 _ _ 𝔵.a_acts.1 𝔵.a_acts.2.1
  have hG : ∀ R, Good 𝔵.A'.J 𝔵.P 𝔵.a₀ ((ev.comp π) R) fun x => ((val x 𝔵.Λ 𝔵.t).comp π) R := by
    refine good_poly (ev.comp π) (fun x => (val x 𝔵.Λ 𝔵.t).comp π) (fun c => ?_) (fun t => ?_) (fun y => ?_)
    · simp only [RingHom.comp_apply, hπC, hev.const, val, eval₂Hom_C, eval_C]
      exact good_const c
    · simp only [RingHom.comp_apply, hπC, val, eval₂Hom_C, eval_X]
      cases t with
      | none =>
        rw [hev.amp]
        refine ⟨⟨_, hA, fun x _ v hv => Module.End.mem_eigenspace_iff.1 hv⟩, ?_⟩
        rw [← 𝔢.a_op]
        exact (Hecke₃ E μ _ _ _ 𝔵.pair 𝔵.D _ _ 𝔵.A 𝔵.A' 𝔵.P 𝔵.isP).2 _ 𝔵.a_hecke
      | some y =>
        rw [hev.cen]
        obtain ⟨⟨β, hk, hc, hz⟩, hP⟩ := genZ 𝔵 y
        refine ⟨⟨_, (actLaws 𝔵.A'.J).2.1 _ _ hk hc, fun x _ v hv => ?_⟩, hP⟩
        have hv' : 𝔵.a₀ v = (x : ℂ) • v := Module.End.mem_eigenspace_iff.1 hv
        rw [hz, ContinuousLinearMap.smul_apply, hv', smul_smul, mul_comm]
        rfl
    · simp only [RingHom.comp_apply, hπX]
      by_cases hy : y.1 ∈ 𝔢.S
      · simp only [if_pos hy, map_zero]
        simpa only [zero_smul] using good_const (J := 𝔵.A'.J) (P := 𝔵.P) (a := 𝔵.a₀) 0
      · obtain ⟨w, i⟩ := y
        simp only [if_neg hy, val, eval₂Hom_X']
        rw [hev.hecke w hy i]
        obtain ⟨⟨s, hs, hz⟩, hP⟩ := genT 𝔵 w hy i
        refine ⟨⟨s, hs, fun x hx v hv => ?_⟩, hP⟩
        have hv' : 𝔵.a₀ v = (x : ℂ) • v := Module.End.mem_eigenspace_iff.1 hv
        have h1 : s 0 (𝔵.a₀ v) = hval 𝔵.t (w, i) • 𝔵.a₀ v := DFunLike.congr_fun hz v
        rw [hv', map_smul, smul_comm] at h1
        exact smul_right_injective _ (Complex.ofReal_ne_zero.2 hx.ne') h1
  obtain ⟨e, he⟩ := symb_hom (J := 𝔵.A'.J) (ev.comp π) fun R => (hG R).1.imp fun _ h => h.1
  refine ⟨e, fun R hR => ?_, fun R hR => ?_, fun z c => ?_, fun z => ?_, fun R hR x hx v hv => ?_⟩
  · have := he R
    rwa [RingHom.comp_apply, hπ R hR] at this
  · have := (hG R).2
    rwa [RingHom.comp_apply, hπ R hR] at this
  · have := he (C (C c))
    rw [RingHom.comp_apply, hπC, hev.const] at this
    exact congrFun (actUniq _ _ _ _ this (act_const c)) z
  · have := he (C (X none))
    rw [RingHom.comp_apply, hπC, hev.amp] at this
    exact congrFun (actUniq _ _ _ _ this hA) z
  · obtain ⟨s, hs, hz⟩ := (hG R).1
    have h1 : e 0 R = s 0 := congrFun (actUniq _ _ _ _ (he R) hs) 0
    have h2 := hz x hx v hv
    simp only [RingHom.comp_apply, hπ R hR] at h2
    rw [h1, h2]
