import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.CuspPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.ActLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.DecayA
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.TwistP
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.HeckeP
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.ChebSB
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.SpecSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.PosSymb
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.ProjEx
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.ChebBd

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

section SlopeTestRemainingChoices

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem cheb_cont (η : ℝ) (m : ℕ) : Continuous (cheb η m) := by
  unfold cheb
  exact (Polynomial.continuous _).comp (by fun_prop)

private theorem ev_cheb {K : Type} [Field K] [NumberField K] {n : ℕ} (ψ : PR K n →+* (H →L[ℂ] H))
    (hc : ∀ c : ℂ, ψ (C (C c)) = c • 1) (A : H →L[ℂ] H) (hA : ψ (C (X none)) = A) (hsa : IsSelfAdjoint A)
    (η : ℝ) (m : ℕ) : ψ (chebP η m) = fcalc (cheb η m) A := by
  have e1 : fcalc (fun x : ℝ => 2 * x / η - 1) A = ((2 / η : ℝ) : ℂ) • A - 1 := by
    unfold fcalc
    have : (fun x : ℝ => 2 * x / η - 1) = fun x : ℝ => (2 / η) • x - 1 := by
      funext x; simp only [smul_eq_mul]; ring
    rw [this, cfc_sub _ _ A, cfc_smul (2 / η) (fun x : ℝ => x) A, cfc_id' ℝ A, cfc_const_one ℝ A]
    rfl
  have e2 : fcalc (cheb η m) A =
      Polynomial.aeval (((2 / η : ℝ) : ℂ) • A - 1) (Polynomial.Chebyshev.T ℝ m) := by
    rw [← e1]
    unfold fcalc
    rw [← cfc_polynomial (R := ℝ) (Polynomial.Chebyshev.T ℝ m) (cfc (fun x : ℝ => 2 * x / η - 1) A),
      ← cfc_comp' (fun y => (Polynomial.Chebyshev.T ℝ m).eval y) (fun x : ℝ => 2 * x / η - 1) A]
    rfl
  let φ : MvPolynomial (Option (Ix K n)) ℂ →ₐ[ℤ] (H →L[ℂ] H) := (ψ.comp C).toIntAlgHom
  have e3 : ψ (chebP η m) = φ (Polynomial.aeval (C ((2 / η : ℝ) : ℂ) * X none - 1 : MvPolynomial (Option (Ix K n)) ℂ)
      (Polynomial.Chebyshev.T ℤ m)) := by
    unfold chebP
    rw [← Polynomial.Chebyshev.map_T (algebraMap ℤ ℂ), Polynomial.aeval_map_algebraMap]
    rfl
  have e4 : φ (C ((2 / η : ℝ) : ℂ) * X none - 1) = ((2 / η : ℝ) : ℂ) • A - 1 := by
    rw [map_sub, map_mul, map_one]
    show ψ (C (C _)) * ψ (C (X none)) - 1 = _
    rw [hc, hA, smul_mul_assoc, one_mul]
  rw [e3, ← Polynomial.aeval_algHom_apply, e4, e2, ← Polynomial.Chebyshev.map_T (algebraMap ℤ ℝ),
    Polynomial.aeval_map_algebraMap]

private theorem fcalc_norm_le (A : H →L[ℂ] H) (h0 : 0 ≤ A) (h1 : ‖A‖ ≤ 1) (φ : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ x ∈ Set.Icc (0 : ℝ) 1, |φ x| ≤ c) : ‖fcalc φ A‖ ≤ c := by
  unfold fcalc
  refine norm_cfc_le hc fun x hx => h x ⟨spectrum_nonneg_of_nonneg h0 hx, ?_⟩
  rcases subsingleton_or_nontrivial (H →L[ℂ] H) with hs | hs
  · simp [spectrum.of_subsingleton] at hx
  · exact (le_abs_self x).trans ((spectrum.norm_le_norm_of_mem hx).trans h1)

omit [CompleteSpace H] in
private theorem norm_pow_le_clm (U : H →L[ℂ] H) (j : ℕ) : ‖U ^ j‖ ≤ ‖U‖ ^ j := by
  rcases j with _ | j
  · rw [pow_zero, pow_zero]
    exact ContinuousLinearMap.norm_id_le
  · exact norm_pow_le' U j.succ_pos

private theorem off_est (A Q W E : H →L[ℂ] H) (h0 : 0 ≤ A) (h1 : ‖A‖ ≤ 1) (hQ : Commute A Q) (hW : Commute W E)
    (e : ℝ) (he : 1 ≤ e) (hE : ‖E‖ ≤ e) (η c : ℝ) (hc : 0 ≤ c) (t χ : ℝ → ℝ) (ht : Continuous t) (hχ : Continuous χ)
    (ht1 : ∀ x ∈ Set.Icc 0 η, |t x| ≤ 1) (ht2 : ∀ x ∈ Set.Icc (0 : ℝ) 1, |t x| ≤ c)
    (hχ1 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (hχ2 : ∀ x ≥ η, χ x = 1) :
    ‖fcalc t A * Q * W * E‖ ≤ e * (‖Q‖ + c * ‖Q * (fcalc χ A * E)‖) * ‖W‖ := by
  have hsa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg h0
  have hcm : Commute (fcalc χ A) Q := hQ.cfc_real χ
  have e1 : fcalc t A = fcalc (fun x => t x * (1 - χ x)) A + fcalc t A * fcalc χ A := by
    unfold fcalc
    rw [← cfc_mul t χ A, ← cfc_add A _ _]
    congr 1
    funext x; ring
  have n1 : ‖fcalc (fun x => t x * (1 - χ x)) A‖ ≤ 1 := by
    refine fcalc_norm_le A h0 h1 _ 1 zero_le_one fun x hx => ?_
    rcases le_total x η with h | h
    · rw [abs_mul]
      have : |1 - χ x| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hχ1 x]
      exact mul_le_one₀ (ht1 x ⟨hx.1, h⟩) (abs_nonneg _) this
    · simp [hχ2 x h]
  have n2 := fcalc_norm_le A h0 h1 t c hc ht2
  have e2 : fcalc t A * Q * W * E =
      (fcalc (fun x => t x * (1 - χ x)) A * (Q * E) + fcalc t A * (Q * (fcalc χ A * E))) * W := by
    rw [mul_assoc _ W, hW.eq, ← mul_assoc]
    congr 1
    conv_lhs => rw [e1]
    rw [add_mul, add_mul, mul_assoc (fcalc t A), hcm.eq]
    simp only [mul_assoc]
  rw [e2, mul_add e]
  refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ((norm_add_le _ _).trans (add_le_add ?_ ?_)) (norm_nonneg _))
  · calc _ ≤ 1 * (‖Q‖ * e) := (norm_mul_le _ _).trans
          (mul_le_mul n1 ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hE (norm_nonneg _))) (norm_nonneg _) zero_le_one)
      _ = e * ‖Q‖ := by ring
  · refine ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right n2 (norm_nonneg _))).trans ?_
    exact le_mul_of_one_le_left (by positivity) he

private theorem conv_twist {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (J : L V →ₗᵢ[ℂ] H) (J' : L W →ₗᵢ[ℂ] H) (U Y : H →L[ℂ] H) (s : V →L[ℂ] W)
    (hs : ∀ (u : L V) (v : L W), (∀ᵐ x : ℝ, v x = s (u x)) → U (J u) = J' v)
    (κ : ℝ → W →L[ℂ] W) (hκ : Ker κ) (hY : Conv J' J' Y κ) :
    Ker (fun t => κ t ∘L s) ∧ Conv J J' (Y ∘L U) (fun t => κ t ∘L s) ∧
      ∀ z, symb (fun t => κ t ∘L s) z = symb κ z ∘L s := by
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  refine ⟨⟨hκ.1.clm_comp continuous_const, ?_⟩, fun u v huv => ?_, fun z => ?_⟩
  · exact hκ.2.comp_left (g := fun k : W →L[ℂ] W => k ∘L s) (by simp)
  · have hw : ∀ᵐ x : ℝ, s.compLp u x = s (u x) := s.coeFn_compLp u
    rw [ContinuousLinearMap.comp_apply, hs u _ hw]
    refine hY _ _ (huv.mono fun x hx => ?_)
    rw [hx]
    refine integral_congr_ae ?_
    filter_upwards [(measurePreserving_add_left volume x).quasiMeasurePreserving.ae hw] with t ht
    rw [ht]; rfl
  · have hi : Integrable fun t : ℝ => Complex.exp (z * t) • κ t :=
      Continuous.integrable_of_hasCompactSupport
        (Continuous.smul (f := fun t : ℝ => Complex.exp (z * t)) (g := κ) (by fun_prop) hκ.1)
        (hκ.2.mono fun t ht h0 => ht (by simp only [h0, smul_zero]))
    have := ((ContinuousLinearMap.compL ℂ V W W).flip s).integral_comp_comm hi
    unfold symb
    simpa using this

private theorem val_cheb {K : Type} [Field K] [NumberField K] {n : ℕ} (x : ℝ) (Λ : (K →+* ℂ) → Multiset ℂ)
    (t : Pl K → Multiset ℂ) (η : ℝ) (m : ℕ) : val x Λ t (chebP η m : PR K n) = (cheb η m x : ℂ) := by
  unfold val chebP cheb
  rw [eval₂Hom_C, ← Polynomial.Chebyshev.map_T (algebraMap ℝ ℂ), Polynomial.aeval_map_algebraMap]
  have := Polynomial.aeval_algHom_apply ((aeval fun o : Option (Ix K n) => o.elim (x : ℂ) fun y => x * (Λ y.1).esymm (y.2 + 1) : MvPolynomial (Option (Ix K n)) ℂ →ₐ[ℂ] ℂ).restrictScalars ℝ)
    (C ((2 / η : ℝ) : ℂ) * X none - 1 : MvPolynomial (Option (Ix K n)) ℂ) (Polynomial.Chebyshev.T ℝ m)
  refine this.symm.trans ?_
  have e : ((aeval fun o : Option (Ix K n) => o.elim (x : ℂ) fun y => x * (Λ y.1).esymm (y.2 + 1) : MvPolynomial (Option (Ix K n)) ℂ →ₐ[ℂ] ℂ).restrictScalars ℝ)
    (C ((2 / η : ℝ) : ℂ) * X none - 1 : MvPolynomial (Option (Ix K n)) ℂ) = algebraMap ℝ ℂ (2 * x / η - 1) := by
    simp; ring
  rw [e, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
  rfl

private theorem act_pow {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V]
    (J : L V →ₗᵢ[ℂ] H) (Y : H →L[ℂ] H) (s : ℂ → V →L[ℂ] V) (h : Act J Y s) (j : ℕ) : Act J (Y ^ j) fun z => s z ^ j := by
  induction j with
  | zero => simpa using (actLaws J).1
  | succ j ih =>
    have := ((actLaws J).2.2.2.1 _ _ _ _ ih h).2
    simp only [pow_succ]
    exact this

end SlopeTestRemainingChoices

set_option maxHeartbeats 800000 in
private theorem fam_part (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (μ : Measure (normOneGL K (2 + 2)))
    [μ.IsHaarMeasure] (θ : Twist μ)
    (𝔰 : Side θ 2) (𝔵 : Fam 𝔰) (ev : PR K (2 + 2) →+* (LL μ →L[ℂ] LL μ)) (evz : ℂ → PR K (2 + 2) →+* (Eu 𝔵.d' →L[ℂ] Eu 𝔵.d'))
    (Nn : Eu 𝔵.d' ≃ₗᵢ[ℂ] Eu 𝔵.d) (C₀ : ℝ) (hev : 𝔰.toAmp.IsEv ev) (hz : 𝔵.IsEvz ev evz)
    (hF : Family μ 𝔵.A 𝔵.A' 0 𝔵.P Nn C₀) (sp : Finset ℝ)
    (hsp : ∀ x, x ∈ sp ↔ 0 < x ∧ Module.End.eigenspace (𝔵.a₀ : Eu 𝔵.d' →ₗ[ℂ] Eu 𝔵.d') (x : ℂ) ≠ ⊥)
    (h0 : 0 ≤ 𝔰.toAmp.A) (h1 : ‖𝔰.toAmp.A‖ ≤ 1) :
    ∃ B cu M₁ : ℝ, 0 ≤ B ∧ 0 ≤ cu ∧ 4 ≤ M₁ ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ (Q : PR K (2 + 2)) (KQ : ℝ),
      (∀ y ∈ Q.vars, y.1 ∉ 𝔰.S) → SB (fun z => evz z Q) KQ →
      ∀ (m j : ℕ) (T : ℝ) (f : TG K (2 + 2)) (Λ : L2 μ →L[ℂ] L2 μ), 0 ≤ T → IsTrunc 𝔵.A.J 𝔵.A'.J T Λ →
        Rop μ f = 𝔰.toAmp.A ∘L (ev (chebP η m * Q) ∘L (𝔰.Uq 0 ^ j)) ∘L Rop μ 𝔰.g →
        IsTraceClass (Λ ∘L (Rop μ f ∘L θ.U) ∘L 𝔵.P ∘L Λ) →
        ‖trace (Λ ∘L (Rop μ f ∘L θ.U) ∘L 𝔵.P ∘L Λ) -
          (1 / 2 : ℂ) * ∑ x ∈ sp, (cheb η m x : ℂ) * (x * val x 𝔵.Λ 𝔵.t Q * 𝔵.tr Nn x j)‖ ≤
          B * cu ^ j * ((M₁ / η) ^ m * KQ * Real.exp (-2 * T)) := by
  obtain ⟨-, l2, l3, l4, l5⟩ := actLaws 𝔵.A'.J
  have pair' : Pair (BW.mu1 K 2) 𝔵.τ₂ 𝔵.τ₁ := ⟨𝔵.pair.irr₂, 𝔵.pair.irr₁, 𝔵.pair.orth.symm⟩
  obtain ⟨Ca, hCa⟩ := decayA K μ _ _ _ pair' 𝔵.D _ _ 𝔵.A' 𝔵.A 𝔰.a 𝔵.βa 𝔰.a_smooth 𝔵.a_acts
  have hvA : ∀ y ∈ (C (X none) : PR K (2 + 2)).vars, y.1 ∉ 𝔰.S := by simp [vars_C]
  obtain ⟨M₀, hM₀⟩ := (l3 _ _ (hz.act _ hvA)).1
  obtain ⟨M₁, hM₁, hch⟩ := chebSB evz hz.const M₀ hM₀
  obtain ⟨cu, hcu⟩ := (l3 _ _ (𝔵.u_act 0)).1
  have ag := l2 _ _ 𝔵.g_acts.1 𝔵.g_acts.2.1
  obtain ⟨Kg, hKg⟩ := (l3 _ _ ag).1
  have z0 : |(0 : ℂ).re| ≤ 1 := by simp
  have hcu0 : 0 ≤ cu := (norm_nonneg _).trans (hcu 0 z0)
  have hKg0 : 0 ≤ Kg := (norm_nonneg _).trans (hKg 0 z0)
  have hCa0 : 0 ≤ Ca := by simpa using (norm_nonneg _).trans (hCa 0 z0)
  refine ⟨|C₀| * Ca * Kg, cu, M₁, by positivity, hcu0, hM₁, fun η hη hη1 Q KQ hQ hKQ m j T f Λ hT hΛ hf htc => ?_⟩
  have hKQ0 : 0 ≤ KQ := (norm_nonneg _).trans (hKQ 0 z0)
  have hM : 0 ≤ (M₁ / η) ^ m := by have : 0 ≤ M₁ := by linarith
                                   positivity
  have hvR : ∀ y ∈ (chebP η m * Q : PR K (2 + 2)).vars, y.1 ∉ 𝔰.S := by
    classical
    intro y hy
    rcases Finset.mem_union.1 (vars_mul _ _ hy) with h | h
    · simp [chebP, vars_C] at h
    · exact hQ y h
  have a1 := (l4 _ _ _ _ (l4 _ _ _ _ (hz.act _ hvR) (act_pow _ _ _ (𝔵.u_act 0) j)).2 ag).2
  obtain ⟨κ, hκ, hκc, hκs⟩ := l5 _ _ _ _ 𝔵.a_acts.1 𝔵.a_acts.2.1 a1
  rw [𝔰.a_op, ← hf] at hκc
  obtain ⟨k1, k2, k3⟩ := conv_twist 𝔵.A.J 𝔵.A'.J θ.U (Rop μ f) (𝔵.s.toContinuousLinearEquiv : Eu 𝔵.d →L[ℂ] Eu 𝔵.d')
    𝔵.s_op κ hκ hκc
  have cP : Commute (Rop μ f * θ.U) 𝔵.P := by
    have c1 : Commute 𝔰.toAmp.A 𝔵.P := by rw [← hev.amp]; exact hz.comm _ hvA
    have c2 : Commute (ev (chebP η m * Q)) 𝔵.P := hz.comm _ hvR
    have c3 : Commute (𝔰.Uq 0) 𝔵.P := 𝔵.u_comm
    have c4 : Commute (Rop μ 𝔰.g) 𝔵.P := (Hecke₃ K μ _ _ _ 𝔵.pair 𝔵.D _ _ 𝔵.A 𝔵.A' _ 𝔵.isP).2 _ 𝔵.g_hecke
    have c5 : Commute θ.U 𝔵.P := (twistP 𝔵).1
    rw [hf]
    exact (c1.mul_left ((c2.mul_left (c3.pow_left j)).mul_left c4)).mul_left c5
  have hs1 : ‖(𝔵.s.toContinuousLinearEquiv : Eu 𝔵.d →L[ℂ] Eu 𝔵.d')‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by simp
  have hb : ∀ z : ℂ, |z.re| ≤ 1 → ‖symb (fun t => κ t ∘L (𝔵.s.toContinuousLinearEquiv : Eu 𝔵.d →L[ℂ] Eu 𝔵.d')) z‖ ≤
      (Ca * ((M₁ / η) ^ m * KQ * cu ^ j * Kg)) / (1 + |z.im|) := by
    intro z hz1
    rw [k3, hκs, mul_div_right_comm]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ((mul_le_of_le_one_right (norm_nonneg _) hs1).trans ?_)
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul (hCa z hz1) ?_ (norm_nonneg _) (by positivity))
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul ?_ (hKg z hz1) (norm_nonneg _) (by positivity))
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity))
    · rw [map_mul]
      exact (norm_mul_le _ _).trans (mul_le_mul (hch η hη hη1 m z hz1) (hKQ z hz1) (norm_nonneg _) hM)
    · exact (norm_pow_le_clm _ j).trans (pow_le_pow_left₀ (norm_nonneg _) (hcu z hz1) j)
  have key := hF.2 (Rop μ f ∘L θ.U) Λ _ T _ k1 k2 cP.eq hT hΛ htc hb
  have hpos : 0 ≤ 𝔵.a₀ := (posSymb 𝔵.A'.J _ _ 𝔵.a_acts.1 𝔵.a_acts.2.1 (𝔰.a_op ▸ h0) (𝔰.a_op ▸ h1)).1
  have hcm : Commute 𝔵.a₀ (evz 0 (chebP η m * Q)) := by
    unfold Fam.a₀
    rw [← hz.amp]
    exact (Commute.all _ _).map (evz 0)
  have hsum := specSum 𝔵.a₀ (evz 0 (chebP η m * Q)) ((𝔵.u 0 0 ^ j) ∘L symb 𝔵.βg 0)
    (Nn.toLinearEquiv : Eu 𝔵.d' →ₗ[ℂ] Eu 𝔵.d) (𝔵.s.toLinearEquiv : Eu 𝔵.d →ₗ[ℂ] Eu 𝔵.d')
    (fun x => val x 𝔵.Λ 𝔵.t (chebP η m * Q)) sp hpos hcm hsp (hz.zero _ hvR)
  have e : ∑ x ∈ sp, (cheb η m x : ℂ) * (x * val x 𝔵.Λ 𝔵.t Q * 𝔵.tr Nn x j) =
      LinearMap.trace ℂ (Eu 𝔵.d) ((Nn.toLinearEquiv : Eu 𝔵.d' →ₗ[ℂ] Eu 𝔵.d) ∘ₗ
        (symb (fun t => κ t ∘L (𝔵.s.toContinuousLinearEquiv : Eu 𝔵.d →L[ℂ] Eu 𝔵.d')) 0 : Eu 𝔵.d →ₗ[ℂ] Eu 𝔵.d')) := by
    rw [k3, hκs]
    refine Eq.trans ?_ hsum.symm
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_mul, val_cheb]
    unfold Fam.tr
    ring
  rw [e]
  refine key.trans ?_
  calc C₀ * (Ca * ((M₁ / η) ^ m * KQ * cu ^ j * Kg)) * Real.exp (-2 * T)
      ≤ |C₀| * (Ca * ((M₁ / η) ^ m * KQ * cu ^ j * Kg)) * Real.exp (-2 * T) := by
        have := le_abs_self C₀
        gcongr
    _ = _ := by ring

private theorem final_arith (C C₁ B e u q r k zN zN' w x y p : ℝ) (hB : 0 ≤ B) (he : 1 ≤ e) (hu : 0 ≤ u) (hq : 0 ≤ q)
    (hr : 0 ≤ r) (hk : 0 ≤ k) (hz : 1 ≤ zN) (hz' : 0 ≤ zN') (hw : 0 ≤ w) (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hp0 : 0 ≤ p)
    (hx : x ≤ e * (q + k * r) * u) (hy : y ≤ k * q * u) (hp : p ≤ u) :
    C * zN * x + C * zN' * y + C₁ * p * q + B * u * w ≤
      (|C| * e + |C₁| + B) * u * (zN * (q + k * r) + k * zN' * q + w) := by
  have hz0 : 0 ≤ zN := zero_le_one.trans hz
  have he0 : 0 ≤ e := zero_le_one.trans he
  have h1 : C * zN * x ≤ |C| * zN * (e * (q + k * r) * u) := by
    have := le_abs_self C
    gcongr
  have h2 : C * zN' * y ≤ |C| * zN' * (e * (k * q * u)) := by
    have := le_abs_self C
    have : y ≤ e * (k * q * u) := hy.trans (le_mul_of_one_le_left (by positivity) he)
    gcongr
  have h3 : q ≤ zN * (q + k * r) + k * zN' * q + w := by
    have a : 0 ≤ k * r := by positivity
    have b : 0 ≤ k * zN' * q := by positivity
    nlinarith
  have h4 : C₁ * p * q ≤ |C₁| * u * (zN * (q + k * r) + k * zN' * q + w) := by
    have := le_abs_self C₁
    gcongr
  have h5 : B * u * w ≤ B * u * (zN * (q + k * r) + k * zN' * q + w) := by
    have : 0 ≤ zN * (q + k * r) + k * zN' * q := by positivity
    gcongr
    linarith
  have h6 : 0 ≤ |C| * e * u * w := by positivity
  nlinarith

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.oneSideX :
    KernX → EvEx → OneSideX := by
  intro hK hEv K _ _ _ μ _ θ 𝔰 𝔵 ev evz Nn C₀ hev hin hz hF sp hsp
  obtain ⟨h0, h1, -, -⟩ := hEv K (2 + 2) (by norm_num) μ 𝔰.toAmp
  obtain ⟨B, cu, M₁, hB, hcu, hM₁, hfam⟩ := fam_part K μ θ 𝔰 𝔵 ev evz Nn C₀ hev hz hF sp hsp h0 h1
  obtain ⟨c, hc, N, hN⟩ := hK K μ _ _ _ 𝔵.pair 𝔵.D _ _ 𝔵.A 𝔵.A' θ 𝔰.a 𝔰.g 𝔵.P 𝔵.isP (twistP 𝔵).1
    (fun T Λ _ h => (twistP 𝔵).2 T Λ h) 𝔰.a_smooth 𝔵.a_hecke 𝔰.g_smooth 𝔵.g_hecke
  obtain ⟨C₁, hC₁⟩ := cuspPart K (2 + 2) 2 (by norm_num) μ θ 𝔰 ev hev hin
  refine ⟨c, max 1 (max cu ‖𝔰.Uq 0‖), M₁, N, hc, le_max_left _ _, hM₁, fun η hη hη1 χ hχ hχ1 hχ2 => ?_⟩
  obtain ⟨s, hs1, hs2, hs3⟩ := hC₁ η hη hη1
  refine ⟨s, hs1, hs2, fun N' => ?_⟩
  obtain ⟨C', T₁, hC⟩ := hN N'
  refine ⟨|C'| * max 1 ‖1 - Pc μ - 𝔵.P‖ + |C₁| + B, max T₁ 0, fun Q a KQ hQ hKQ ha m j T f hT hf => ?_⟩
  have hT0 : 0 ≤ T := (le_max_right _ _).trans hT
  obtain ⟨Λ, hΛ⟩ := (projEx K μ _ _ _ 𝔵.pair 𝔵.D _ _ 𝔵.A 𝔵.A').2 T hT0
  have hsa : IsSelfAdjoint 𝔰.toAmp.A := IsSelfAdjoint.of_nonneg h0
  have hPc : prj (cuspidalL2 μ) = Pc μ := by
    unfold prj Pc
    congr 1
    exact (isClosed_cuspidalL2 μ).submodule_topologicalClosure_eq
  have hcP : ∀ T, Inner μ T → Commute T (Pc μ) := fun T hT => by
    rw [← hPc]; exact hT _ (isClosed_cuspidalL2 μ) (isInvariant_cuspidalL2 μ)
  have hQA : Commute 𝔰.toAmp.A (ev Q) := hev.amp ▸ (Commute.all _ Q).map ev
  have hvR : ∀ y ∈ (chebP η m * Q : PR K (2 + 2)).vars, y.1 ∉ 𝔰.S := by
    classical
    intro y hy
    rcases Finset.mem_union.1 (vars_mul _ _ hy) with h | h
    · simp [chebP, vars_C] at h
    · exact hQ y h
  obtain ⟨hb1, hb2, -⟩ := FX.cheb_bound η m hη hη1
  have hk : 0 ≤ (4 / η) ^ m := by positivity
  have hch : ev (chebP η m * Q) = fcalc (cheb η m) 𝔰.toAmp.A * ev Q := by
    rw [map_mul, ev_cheb ev hev.const _ hev.amp hsa]
  have hUc : Commute (𝔰.Uq 0 ^ j) (Pc μ) := (hcP _ (𝔰.Uq_inner 0)).pow_left j
  have hUP : Commute (𝔰.Uq 0 ^ j) 𝔵.P := (show Commute (𝔰.Uq 0) 𝔵.P from 𝔵.u_comm).pow_left j
  have hMc : Commute (ev (chebP η m * Q) * 𝔰.Uq 0 ^ j) (Pc μ) := (hcP _ (hin _)).mul_left hUc
  have hMP : Commute (ev (chebP η m * Q) * 𝔰.Uq 0 ^ j) 𝔵.P :=
    (show Commute (ev (chebP η m * Q)) 𝔵.P from hz.comm _ hvR).mul_left hUP
  obtain ⟨htc, k1⟩ := hC f (ev (chebP η m * Q) * 𝔰.Uq 0 ^ j) Λ T ((le_max_left _ _).trans hT) hT0 hMc.eq hMP.eq
    (by rw [𝔰.a_op]; exact hf.1) hΛ hf.2
  have hp : ‖𝔰.Uq 0‖ ^ j ≤ max 1 (max cu ‖𝔰.Uq 0‖) ^ j :=
    pow_le_pow_left₀ (norm_nonneg _) ((le_max_right _ _).trans (le_max_right _ _)) j
  have hu := (norm_pow_le_clm (𝔰.Uq 0) j).trans hp
  have k2 := off_est 𝔰.toAmp.A (ev Q) (𝔰.Uq 0 ^ j) (1 - Pc μ - 𝔵.P) h0 h1 hQA
    (((Commute.one_right _).sub_right hUc).sub_right hUP) _ (le_max_left 1 _) (le_max_right _ _) η _ hk (cheb η m) χ
    (cheb_cont η m) hχ hb1 hb2 hχ1 hχ2
  have k2' := k2.trans (mul_le_mul_of_nonneg_left hu (by positivity))
  rw [← hch] at k2'
  have k3 : ‖ev (chebP η m * Q) * 𝔰.Uq 0 ^ j‖ ≤ (4 / η) ^ m * ‖ev Q‖ * max 1 (max cu ‖𝔰.Uq 0‖) ^ j := by
    rw [hch]
    refine (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans ?_) hu (norm_nonneg _) (by positivity))
    exact mul_le_mul_of_nonneg_right (fcalc_norm_le _ h0 h1 _ _ hk hb2) (norm_nonneg _)
  have k4 := hs3 Q a ha m j f hf.1
  have hw : 0 ≤ (M₁ / η) ^ m * KQ * Real.exp (-2 * T) := by
    have : 0 ≤ M₁ := by linarith
    have : 0 ≤ KQ := (norm_nonneg _).trans (hKQ 0 (by simp))
    positivity
  have k5 := (hfam η hη hη1 Q KQ hQ hKQ m j T f Λ hT0 hΛ hf.1 htc).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hcu ((le_max_left _ ‖𝔰.Uq 0‖).trans (le_max_right 1 _)) j) hB) hw)
  have tri : ∀ x y z u v : ℂ, ‖x - u - v‖ ≤ ‖x - y - z‖ + ‖y - u‖ + ‖z - v‖ := fun x y z u v => by
    have : x - u - v = (x - y - z) + (y - u) + (z - v) := by ring
    rw [this]; exact norm_add₃_le
  refine (tri _ _ _ _ _).trans ((add_le_add (add_le_add k1 k4) k5).trans ?_)
  exact final_arith _ _ _ _ _ _ _ _ _ _ _ _ _ _ hB (le_max_left _ _) (by positivity) (norm_nonneg _) (norm_nonneg _) hk
    (Real.one_le_exp (by positivity)) (Real.exp_nonneg _) hw (norm_nonneg _) (norm_nonneg _) (by positivity) k2' k3 hp
