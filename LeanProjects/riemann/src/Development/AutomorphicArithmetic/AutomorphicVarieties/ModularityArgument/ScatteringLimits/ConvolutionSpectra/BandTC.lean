import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.BandHS
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CarLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.AvApprox
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.AvSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ProjLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvAdj

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W]

private theorem widen (M : Sc H V W) (φ : ℝ → ℂ) (hi : Integrable φ) (ρ a b : ℝ) (hρ : ∀ t, ρ < |t| → φ t = 0) :
    M.P (Ioc (a - ρ) (b + ρ)) * (M.F.av φ * M.P (Ioc a b)) = M.F.av φ * M.P (Ioc a b) := by
  ext h
  obtain ⟨i1, i2⟩ := ((avSpec M.F).2.2.2 φ hi).1 (M.P (Ioc a b) h)
  simp only [ContinuousLinearMap.mul_apply]
  rw [i2, ← ContinuousLinearMap.integral_comp_comm _ i1]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  by_cases ht : ρ < |t|
  · simp [hρ t ht]
  have pl := (projLaws M).2.2.2.2.1
  have m : MeasurableSet ((fun x => x + t) ⁻¹' Ioc a b) := measurableSet_Ioc.preimage (measurable_add_const t)
  have e1 : M.F.U t (M.P (Ioc a b) h) = _ :=
    DFunLike.congr_fun ((pl (Ioc a b) (Ioc a b) measurableSet_Ioc measurableSet_Ioc).2.2.2.2 t).1 h
  have e2 := (pl (Ioc (a - ρ) (b + ρ)) _ measurableSet_Ioc m).1
  rw [inter_eq_right.2 (by
    rintro x ⟨h1, h2⟩
    have := abs_le.1 (not_lt.1 ht)
    constructor <;> linarith [this.1, this.2])] at e2
  simp only [map_smul]
  rw [e1]
  exact congrArg _ (DFunLike.congr_fun e2 _)
end

theorem UpperTheory.V.Z.IntegralApplyAeEq.bandTC :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (X : H →L[ℂ] H) (κ : ℝ → V →L[ℂ] W), Ker κ → M.Carries X κ → ∀ (ψ : ℝ → ℝ) (δ a b : ℝ), Bump ψ (-δ) 0 → a ≤ b →
      IsTraceClass ((M.F.av (fun t => (ψ t : ℂ)) ∘L X) ∘L M.P (Ioc a b)) ∧ IsTraceClass (M.P' (Ioc a b) ∘L (M.F.av (fun t => (ψ t : ℂ)) ∘L X)) ∧
      IsTraceClass ((M.F.av (fun t => (ψ t : ℂ)) ∘L X) ∘L M.P' (Ioc a b)) ∧
      trace ((M.F.av (fun t => (ψ t : ℂ)) ∘L X) ∘L M.P (Ioc a b)) = ∫ y in a..b, ∑ i, M.cor (fun x => (ψ x : ℂ)) (stdOrthonormalBasis ℂ V i) (kv κ (stdOrthonormalBasis ℂ V i)) (2 * y) ∧
      trace (M.P' (Ioc a b) ∘L (M.F.av (fun t => (ψ t : ℂ)) ∘L X)) =
        conj (∫ y in a..b, ∑ j, M.swap.cor (fun x => (ψ (-x) : ℂ)) (stdOrthonormalBasis ℂ W j) (kv (sharp κ) (stdOrthonormalBasis ℂ W j)) (2 * y)) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M X κ hk hX ψ δ a b hψ hab
  obtain ⟨c1, c2, -⟩ := carLaws M X κ hk hX
  have hk' := (convAdj κ hk).1
  obtain ⟨s0, hi, -⟩ := avApprox.2.1 ψ _ _ hψ
  have cc : Continuous fun t => (ψ t : ℂ) := Complex.continuous_ofReal.comp hψ.cont
  have sc : HasCompactSupport fun t => (ψ t : ℂ) := s0.comp_left Complex.ofReal_zero
  have cn : Continuous fun t => (ψ (-t) : ℂ) := cc.comp continuous_neg
  have sn : HasCompactSupport fun t => (ψ (-t) : ℂ) := sc.comp_homeomorph (Homeomorph.neg ℝ)
  have z : ∀ t, |δ| < |t| → ψ t = 0 := fun t ht => hψ.supp t fun h => by
    have : |t| ≤ |δ| := abs_le.2 ⟨by linarith [h.1, le_abs_self δ], h.2.trans (abs_nonneg δ)⟩
    linarith
  obtain ⟨-, -, a1, a2, -⟩ := (avSpec M.F).2.2.2 _ hi
  simp only [Complex.conj_ofReal] at a1
  set Ψ := M.F.av fun t => (ψ t : ℂ) with hΨ
  set Ψn := M.F.av fun t => (ψ (-t) : ℂ) with hΨn
  have a3 : M.swap.F.av (fun t => (ψ t : ℂ)) = Ψn := a2
  have cm : Ψ * X = X * Ψn := by
    have := ((avSpec M.F.rev).2.2.2 _ hi).2.2.2.2 M.F X fun t h => by
      show X (M.F.U (-t) h) = _
      rw [c1, neg_neg]
    rw [a2] at this
    exact this.symm
  have hab' : a - |δ| ≤ b + |δ| := by linarith [abs_nonneg δ]
  have w1 := widen M (fun t => (ψ (-t) : ℂ)) hi.comp_neg |δ| a b fun t ht => by rw [z (-t) (by rwa [abs_neg])]; simp
  have w2 := widen M.swap (fun t => (ψ t : ℂ)) hi |δ| a b fun t ht => by rw [z t ht]; simp
  rw [a3] at w2
  obtain ⟨b1, -, b2, -, b3⟩ := bandHS M X κ hk hX _ a b cn sn hab
  obtain ⟨b4, -⟩ := bandHS M X κ hk hX _ _ _ cn sn hab'
  obtain ⟨d1, -, d2, -, d3⟩ := bandHS M.swap _ _ hk' c2 _ a b cc sc hab
  obtain ⟨d4, -⟩ := bandHS M.swap _ _ hk' c2 _ _ _ cc sc hab'
  rw [a3] at d2 d3
  obtain ⟨p1, p2, -⟩ := (projLaws M).2.2.2.2.1 (Ioc a b) (Ioc a b) measurableSet_Ioc measurableSet_Ioc
  obtain ⟨q1, q2, -⟩ := (projLaws M.swap).2.2.2.2.1 (Ioc a b) (Ioc a b) measurableSet_Ioc measurableSet_Ioc
  obtain ⟨-, q3, -⟩ := (projLaws M.swap).2.2.2.2.1 (Ioc (a - |δ|) (b + |δ|)) (Ioc a b) measurableSet_Ioc measurableSet_Ioc
  rw [inter_self] at p1 q1
  have d5 : IsHilbertSchmidt (X ∘L M.swap.P (Ioc (a - |δ|) (b + |δ|))) := by
    refine flip M.swap X _ _ (fun t h => c1 (-t) h) ?_
    have := d4.adjoint
    rwa [ContinuousLinearMap.adjoint_comp, q3.adjoint_eq, ContinuousLinearMap.adjoint_adjoint] at this
  simp only [Sc.P']
  set P := M.P (Ioc a b)
  set Q := M.swap.P (Ioc a b)
  set P₁ := M.P (Ioc (a - |δ|) (b + |δ|))
  set Q₁ := M.swap.P (Ioc (a - |δ|) (b + |δ|))
  have a1' : star Ψ = Ψn := a1
  have a4 : star Ψn = Ψ := by rw [← a1', star_star]
  have t1 : IsTraceClass (Ψ * X * P) := by
    rw [cm, mul_assoc, ← w1, ← mul_assoc]
    exact isTraceClass_comp b4 b2
  have t3 : IsTraceClass (Ψ * X * Q) := by
    rw [cm, mul_assoc, ← w2, ← mul_assoc]
    exact isTraceClass_comp d5 d2
  have t2 : IsTraceClass (Q * (Ψ * X)) := by
    have h : IsTraceClass (star X * Q₁ * (Ψn * Q)) := isTraceClass_comp d4 d2
    rw [mul_assoc, w2] at h
    have h' : IsTraceClass (star (star X * (Ψn * Q))) := h.adjoint
    rwa [star_mul, star_mul, star_star, q2.star_eq, a4, mul_assoc] at h'
  refine ⟨t1, t2, t3, ?_, ?_⟩
  · simp only [neg_neg] at b3
    rw [← b3]
    have h := trace_comp_comm t1 P
    change trace (P * (Ψ * X * P)) = trace (Ψ * X * P * P) at h
    change P * P = P at p1
    rw [mul_assoc (Ψ * X), p1] at h
    change trace (Ψ * X * P) = trace (star (Ψn * P) * (X * P))
    rw [← h, star_mul, p2.star_eq, a4]
    simp only [mul_assoc]
  · rw [← d3, ← trace_adjoint (isTraceClass_comp d2.adjoint d1)]
    have h := trace_comp_comm t2 Q
    change trace (Q * (Q * (Ψ * X))) = trace (Q * (Ψ * X) * Q) at h
    change Q * Q = Q at q1
    rw [← mul_assoc, q1] at h
    change trace (Q * (Ψ * X)) = trace (star (star (Ψn * Q) * (star X * Q)))
    rw [h, star_mul, star_star, star_mul, star_star, q2.star_eq, cm]
    simp only [mul_assoc]
