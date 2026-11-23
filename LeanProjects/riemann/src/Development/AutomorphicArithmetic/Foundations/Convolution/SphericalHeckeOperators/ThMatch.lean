import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymSum
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Match
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.ElemMatch
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.DefBridge
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.UnrQ

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

private theorem quot_smul {G : Type*} [Group G] [MeasurableSpace G] (μ : Measure G) (H : Subgroup G) (ν : Measure H)
    (c : ℂ) (F : G → ℂ) :
    PositivityTheory.Rg.Tf.Loc.quotIntegral μ H ν (fun g => c * F g) = c * PositivityTheory.Rg.Tf.Loc.quotIntegral μ H ν F := by
  unfold PositivityTheory.Rg.Tf.Loc.quotIntegral
  split_ifs with h
  · rw [← integral_const_mul]
    simp only [mul_assoc]
  · simp

private theorem match_smul {k E : Type} [Field k] [Field E] [Algebra k E] {n : ℕ} [TopologicalSpace k] [TopologicalSpace E]
    [MeasurableSpace (GL (Fin n) E)] [MeasurableSpace (GL (Fin n) k)]
    {σ : E ≃ₐ[k] E} {μE : Measure (GL (Fin n) E)} {μk : Measure (GL (Fin n) k)} {φ : GL (Fin n) E → ℂ} {f : GL (Fin n) k → ℂ}
    (h : UpperTheory.ConvolutionTheory.Loc.Match σ μE μk φ f) (c : ℂ) : UpperTheory.ConvolutionTheory.Loc.Match σ μE μk (c • φ) (c • f) := by
  refine ⟨fun δ γ x μδ μγ h1 h2 h3 h4 h5 => ?_, fun γ μγ h1 h2 h3 => ?_⟩
  · have := h.1 δ γ x μδ μγ h1 h2 h3 h4 h5
    unfold PositivityTheory.Rg.Tf.Loc.twOrbIntegralC PositivityTheory.Rg.Tf.Loc.orbIntegralC at this ⊢
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [quot_smul, quot_smul, this]
  · have := h.2 γ μγ h1 h2 h3
    unfold PositivityTheory.Rg.Tf.Loc.orbIntegralC at this ⊢
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [quot_smul, this, mul_zero]

private theorem half_eq {k E : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {l : ℕ} (hq : qF E = qF k ^ l)
    {n : ℕ} (a : Fin n → ℤ) : halfModulus k ((l : ℤ) • a) = halfModulus E a := by
  have hs : sqrtQ E = sqrtQ k ^ l := by
    have h1 : NNReal.sqrt (qF E : NNReal) = NNReal.sqrt (qF k : NNReal) ^ l := by
      rw [NNReal.sqrt_eq_iff_eq_sq, ← pow_mul, mul_comm, pow_mul, NNReal.sq_sqrt, hq, Nat.cast_pow]
    rw [sqrtQ, sqrtQ, h1, NNReal.coe_pow, Complex.ofReal_pow]
  have hr : rhoPair ((l : ℤ) • a) = (l : ℤ) * rhoPair a := by
    simp only [rhoPair, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [halfModulus_eq, halfModulus_eq, hs, hr, ← zpow_natCast, ← zpow_mul, mul_neg]

private theorem incl_diagPow {k E : Type} [Field k] [Field E] [Algebra k E] {n : ℕ} (ϖ : kˣ) (a : Fin n → ℤ) :
    (PositivityTheory.Rg.Tf.Loc.incl (PositivityTheory.Rg.Tf.Loc.diagPow ϖ a) : GL (Fin n) E) =
      PositivityTheory.Rg.Tf.Loc.diagPow (Units.map (algebraMap k E : k →* E) ϖ) a := by
  ext i j
  change algebraMap k E (Matrix.diagonal (fun i => ((ϖ ^ a i : kˣ) : k)) i j) =
    Matrix.diagonal (fun i => (((Units.map (algebraMap k E : k →* E) ϖ) ^ a i : Eˣ) : E)) i j
  by_cases h : i = j
  · subst h
    simp
  · simp [Matrix.diagonal_apply_ne _ h]

theorem UpperTheory.ConvolutionTheory.H.thMatch :
    ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E], PositivityTheory.Rg.Tf.Loc.IsUnramifiedLoc k E →
      ∀ σ : E ≃ₐ[k] E, (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
      ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)] [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
        (μE : Measure (GL (Fin n) E)) (μk : Measure (GL (Fin n) k)) [μE.IsHaarMeasure] [μk.IsHaarMeasure],
      ∀ a : Fin n → ℤ, StrictAnti a → UpperTheory.ConvolutionTheory.Loc.Match σ μE μk (th μE a) (th μk ((Module.finrank k E : ℤ) • a)) := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ hu σ hσ n _ _ _ _ μE μk hE hk a ha
  obtain ⟨-, hIk, ⟨ϖ, hϖ⟩, hfk⟩ := defBridge k n
  obtain ⟨-, hIE, -, hfE⟩ := defBridge E n
  obtain ⟨hq, hun⟩ := unrQ k E hu
  have h := UpperTheory.ConvolutionTheory.Loc.elemMatch k E hu σ hσ n μE μk hE hk ϖ hϖ a ha
  rw [incl_diagPow, hfE _ (hun ϖ hϖ), hfk ϖ hϖ, hIk, hIE] at h
  have hne : μE.real (iwahori E n : Set (GL (Fin n) E)) ≠ 0 := by
    rw [measureReal_def, ENNReal.toReal_ne_zero]
    exact ⟨((isOpen_iwahori E n).measure_pos μE ⟨1, one_mem _⟩).ne', (isCompact_iwahori E n).measure_lt_top.ne⟩
  have hne' : (μE.real (iwahori E n : Set (GL (Fin n) E)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hne
  have h2 := match_smul h (halfModulus E a / (μE.real (iwahori E n : Set (GL (Fin n) E)) : ℂ))
  rw [smul_smul] at h2
  unfold th
  rw [half_eq hq]
  convert h2 using 2
  · rw [← measureReal_def, ← measureReal_def, Complex.ofReal_div]
    field_simp
  · rfl
