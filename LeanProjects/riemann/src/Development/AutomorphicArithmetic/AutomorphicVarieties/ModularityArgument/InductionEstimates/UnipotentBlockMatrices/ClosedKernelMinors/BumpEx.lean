import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import GroundTheory.AutomorphicForms.L2LocalComponents.ArchBump
import GroundTheory.AutomorphicForms.GKModules.KernelCalculus
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SmoothingFinite

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

section SlopeTestRemainingChoices

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [FirstCountableTopology G]
  [LocallyCompactSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
  [LocallyCompactSpace H]

private theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.bump_cont (ν : Measure H) [ν.IsHaarMeasure] {ρ : H → ℝ} (hρ : Continuous ρ)
    (hρc : HasCompactSupport ρ) {Φ : G → H → ℝ} (hΦ : Continuous (Function.uncurry Φ)) :
    Continuous fun x => ∫ p, ρ p * Φ x p ∂ν := by
  have e : (fun x => ∫ p, ρ p * Φ x p ∂ν) = fun x => ∫ p in tsupport ρ, ρ p * Φ x p ∂ν := by
    funext x
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp => ?_).symm
    rw [image_eq_zero_of_notMem_tsupport hp, zero_mul]
  rw [e]
  exact continuous_parametric_integral_of_continuous ((hρ.comp continuous_snd).mul hΦ) hρc

private theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.bump_split {O : Set G} (hO : O ∈ 𝓝 (1 : G)) :
    ∃ V ∈ 𝓝 (1 : G), ∀ a ∈ V, ∀ b ∈ V, ∀ c ∈ V, a * b * c⁻¹ ∈ O := by
  obtain ⟨V₁, h₁, e₁⟩ := exists_nhds_split_inv hO
  obtain ⟨V₂, h₂, e₂⟩ := exists_nhds_one_split h₁
  refine ⟨V₁ ∩ V₂, inter_mem h₁ h₂, fun a ha b hb c hc => ?_⟩
  rw [← div_eq_mul_inv]
  exact e₁ _ (e₂ a ha.2 b hb.2) c hc.1

private theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.bump_step (ν : Measure H) [ν.IsHaarMeasure] (π : H →* G) (hπ : Continuous π)
    {ρ : H → ℝ} (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) (hρ0 : ∀ p, 0 ≤ ρ p) {p₀ : H} (hρ1 : ρ p₀ ≠ 0)
    {h : G → ℝ} (hh : Continuous h) (hh0 : ∀ x, 0 ≤ h x) (hh1 : h 1 ≠ 0) (hs : ∀ x, h x⁻¹ = h x)
    {O : Set G} (hO : ∀ p q y, ρ p ≠ 0 → ρ q ≠ 0 → h y ≠ 0 → π p * y * (π q)⁻¹ ∈ O) :
    ∃ F a : G → ℝ, Continuous F ∧ (∀ x, a x = ∫ p, ρ p * F ((π p)⁻¹ * x) ∂ν) ∧
      (∀ u, (∀ x, h (u * x) = h x) → ∀ x, F (u * x) = F x) ∧
      Continuous a ∧ (∀ x, 0 ≤ a x) ∧ a 1 ≠ 0 ∧ (∀ x, a x⁻¹ = a x) ∧ ∀ x, a x ≠ 0 → x ∈ O := by
  set F : G → ℝ := fun y => ∫ q, ρ q * h (y * π q) ∂ν with hF
  have hFc : Continuous F := bump_cont ν hρ hρc (Φ := fun y q => h (y * π q))
    (hh.comp (continuous_fst.mul (hπ.comp continuous_snd)))
  have hF0 : ∀ y, 0 ≤ F y := fun y => integral_nonneg fun q => mul_nonneg (hρ0 q) (hh0 _)
  have hF1 : 0 < F (π p₀)⁻¹ := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := p₀)
      (hρ.mul (hh.comp (continuous_const.mul hπ))) hρc.mul_right
      (fun q => mul_nonneg (hρ0 q) (hh0 _)) ?_
    simpa using ⟨hρ1, hh1⟩
  have ha : ∀ x, ∫ p, ρ p * F ((π p)⁻¹ * x) ∂ν = ∫ p, ∫ q, ρ p * (ρ q * h ((π p)⁻¹ * x * π q)) ∂ν ∂ν := by
    intro x
    simp only [hF, integral_const_mul]
  refine ⟨F, fun x => ∫ p, ρ p * F ((π p)⁻¹ * x) ∂ν, hFc, fun _ => rfl, fun u hu x => ?_, ?_,
    fun x => integral_nonneg fun q => mul_nonneg (hρ0 q) (hF0 _), ne_of_gt ?_, fun x => ?_, fun x hx => ?_⟩
  · simp only [hF, mul_assoc, hu]
  · exact bump_cont ν hρ hρc (Φ := fun x p => F ((π p)⁻¹ * x))
      (hFc.comp ((hπ.comp continuous_snd).inv.mul continuous_fst))
  · refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := p₀)
      (hρ.mul (hFc.comp (hπ.inv.mul continuous_const))) hρc.mul_right
      (fun q => mul_nonneg (hρ0 q) (hF0 _)) ?_
    simpa using ⟨hρ1, hF1.ne'⟩
  · beta_reduce
    rw [ha, ha, integral_integral_swap_of_hasCompactSupport]
    · refine integral_congr_ae (Eventually.of_forall fun p => integral_congr_ae (Eventually.of_forall fun q => ?_))
      beta_reduce
      rw [← hs ((π p)⁻¹ * x * π q)]
      simp only [mul_inv_rev, inv_inv, mul_assoc]
      ring
    · exact (hρ.comp continuous_fst).mul ((hρ.comp continuous_snd).mul (hh.comp
        (((hπ.comp continuous_fst).inv.mul continuous_const).mul (hπ.comp continuous_snd))))
    · refine HasCompactSupport.intro (hρc.isCompact.prod hρc.isCompact) fun z hz => ?_
      rw [mem_prod, not_and_or] at hz
      rcases hz with hz | hz <;> simp [Function.uncurry, image_eq_zero_of_notMem_tsupport hz]
  · by_contra hxO
    refine hx ?_
    beta_reduce
    rw [ha]
    have : ∀ p q, ρ p * (ρ q * h ((π p)⁻¹ * x * π q)) = 0 := by
      intro p q
      by_contra h0
      refine hxO ?_
      have := hO p q _ (left_ne_zero_of_mul h0) (left_ne_zero_of_mul (right_ne_zero_of_mul h0))
        (right_ne_zero_of_mul (right_ne_zero_of_mul h0))
      simpa [mul_assoc] using this
    simp [this]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.bumpEx :
    ∀ {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (O : Set (G1 K n)), O ∈ 𝓝 (1 : G1 K n) →
      ∃ a : CC K n, tsupport a ⊆ O ∧ (∀ g, 0 ≤ (a g).re ∧ (a g).im = 0) ∧ ∫ g, a g ∂μ = 1 ∧ CuspidalProjection.ccStar a = a ∧ UpperTheory.ConvolutionTheory.C.IsLeftSmooth a := by
  intro K _ _ n μ _ O hO
  obtain ⟨O', hO', hO'O, hO'c⟩ := local_compact_nhds hO
  obtain ⟨V₂, hV₂, e₂⟩ := bump_split hO'
  obtain ⟨V₁, hV₁, e₁⟩ := bump_split hV₂

  obtain ⟨f, hf1, hf0, -, hf⟩ := exists_continuous_one_zero_of_isCompact (isCompact_singleton (x := (1 : G1 K n)))
    (isOpen_interior (s := V₁)).isClosed_compl
    (disjoint_singleton_left.2 fun h => h (mem_interior_iff_mem_nhds.2 hV₁))
  have hf1' : f 1 = 1 := hf1 rfl
  have hfV : ∀ y, f y ≠ 0 → y ∈ V₁ := fun y hy => by
    by_contra hn
    exact hy (hf0 fun h => hn (interior_subset h))

  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    ((isOpen_interior (s := V₁)).preimage (continuous_finOne (K := K) (n := n)))
    (by rw [mem_preimage, map_one]; exact mem_interior_iff_mem_nhds.2 hV₁)
  set U : Subgroup (AdelicGLn.integralFiniteGL K n) := N.toOpenSubgroup.toSubgroup
  have hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) := N.toOpenSubgroup.isOpen
  have hUV : ∀ u : U, finOne K n u ∈ V₁ := fun u => interior_subset (hN u.2)
  have := compactSpace_of_isOpen U hU
  obtain ⟨F₁, h, -, hF₁, -, hc, h0, h1, hs, hV⟩ := bump_step (haarProb U) ((finOne K n).comp U.subtype)
    (continuous_finOne.comp continuous_subtype_val) (ρ := fun _ => 1) continuous_const
    (HasCompactSupport.of_compactSpace _) (fun _ => zero_le_one) (p₀ := 1) one_ne_zero (h := fun x => f x * f x⁻¹)
    (f.continuous.mul (f.continuous.comp continuous_inv)) (fun x => mul_nonneg (hf _).1 (hf _).1)
    (by simp [hf1']) (fun x => by simp [mul_comm]) (O := V₂)
    (fun p q y _ _ hy => e₁ _ (hUV p) _ (hfV _ (left_ne_zero_of_mul hy)) _ (hUV q))
  have hinv : ∀ u ∈ U, ∀ x, h (finOne K n u * x) = h x := by
    intro u hu x
    rw [hF₁, hF₁, ← integral_mul_left_eq_self _ (⟨u, hu⟩ : U)]
    simp [mul_assoc]

  let ν : Measure (archGroup K n) := Measure.haar
  obtain ⟨ρ, hρ0, hρt, hρ1, -, -, hρN, -⟩ := exists_archBump ν (N := archP K n ⁻¹' V₂)
    (continuous_archP.continuousAt.preimage_mem_nhds (by rwa [map_one]))
  have hρc : Continuous ρ := Complex.continuous_re.comp (hρt.continuous _)
  have hρs : HasCompactSupport ρ := hρt.2.comp_left (g := Complex.re) rfl
  obtain ⟨p₀, hp₀⟩ : ∃ p, ρ p ≠ 0 := by
    by_contra hn
    push Not at hn
    simp [hn] at hρ1
  obtain ⟨F, a, hFc, hF, hFi, ac, a0, a1, as, aO⟩ := bump_step ν (archP K n) continuous_archP hρc hρs hρ0 hp₀ hc h0 h1 hs
    (O := O') (fun p q y hp hq hy => e₂ _ (hρN p hp) _ (hV y hy) _ (hρN q hq))
  have acs : HasCompactSupport a := HasCompactSupport.intro hO'c fun x hx => by
    by_contra hn
    exact hx (aO x hn)
  have hI : 0 < ∫ x, a x ∂μ := ac.integral_pos_of_hasCompactSupport_nonneg_nonzero acs a0 a1
  set I := ∫ x, a x ∂μ with hIdef
  refine ⟨⟨⟨fun x => ((a x * I⁻¹ : ℝ) : ℂ), Complex.continuous_ofReal.comp (ac.mul continuous_const)⟩,
    HasCompactSupport.comp_left (g := Complex.ofReal) (f := fun x => a x * I⁻¹) acs.mul_right Complex.ofReal_zero⟩,
    ?_, fun g => ⟨?_, Complex.ofReal_im _⟩, ?_, ?_, fun x => ?_, U, hU, fun u hu x => ?_⟩
  · refine Subset.trans (closure_minimal (fun x hx => aO x fun h0 => ?_) hO'c.isClosed) hO'O
    have hx' : ((a x * I⁻¹ : ℝ) : ℂ) ≠ 0 := hx
    simp [h0] at hx'
  · exact mul_nonneg (a0 g) (inv_nonneg.2 hI.le)
  · change ∫ x, ((a x * I⁻¹ : ℝ) : ℂ) ∂μ = 1
    rw [integral_complex_ofReal, integral_mul_const, mul_inv_cancel₀ hI.ne', Complex.ofReal_one]
  · ext g
    change conj ((a g⁻¹ * I⁻¹ : ℝ) : ℂ) = ((a g * I⁻¹ : ℝ) : ℂ)
    rw [Complex.conj_ofReal, as]
  · change (isExpLieAlgebra K n).IsSmoothFun fun A => ((a (archP K n A * x) * I⁻¹ : ℝ) : ℂ)
    have hΨ : Continuous fun y : archGroup K n => ((F ((archP K n y)⁻¹ * x) * I⁻¹ : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp ((hFc.comp (continuous_archP.inv.mul continuous_const)).mul continuous_const)
    have hsm := IsExpLieAlgebra.isSmoothFun_comp_inv ((isExpLieAlgebra K n).isSmoothFun_integral_mul ν hΨ hρt)
    convert hsm using 2 with A
    rw [hF, ← integral_mul_const, ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [map_mul, map_inv, mul_inv_rev, inv_inv, mul_assoc]
    push_cast
    ring
  · change ((a (finOne K n u * x) * I⁻¹ : ℝ) : ℂ) = ((a x * I⁻¹ : ℝ) : ℂ)
    rw [hF, hF]
    simp only [archimedeanProjection_apply, ← mul_assoc, archProj_inv_mul_finOne]
    simp only [mul_assoc, hFi _ (hinv u hu)]
