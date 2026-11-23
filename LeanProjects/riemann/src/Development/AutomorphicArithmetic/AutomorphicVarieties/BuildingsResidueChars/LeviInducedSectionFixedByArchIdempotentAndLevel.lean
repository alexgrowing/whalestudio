import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.UnipBlocks
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MaximalCompactUniqueArchFiniteDecomposition

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace
open scoped NumberField.AdeleRing

private theorem cont_int {X : Type*} [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] {f : X → ℂ}
    (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

private theorem swap3 {A V : Type*} [TopologicalSpace A] [CompactSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [TopologicalSpace V] [CompactSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] (κ : Measure A) (ρ : Measure V) [IsFiniteMeasure κ] [IsFiniteMeasure ρ]
    (G : A → V → V → ℂ) (hG : Continuous fun p : A × V × V => G p.1 p.2.1 p.2.2) :
    ∫ a, ∫ v₁, ∫ v₂, G a v₁ v₂ ∂ρ ∂ρ ∂κ = ∫ v₁, ∫ v₂, ∫ a, G a v₁ v₂ ∂κ ∂ρ ∂ρ := by
  have h1 : Integrable (Function.uncurry fun a v₁ => ∫ v₂, G a v₁ v₂ ∂ρ) (κ.prod ρ) := by
    have h : Integrable (fun p : (A × V) × V => G p.1.1 p.1.2 p.2) ((κ.prod ρ).prod ρ) :=
      cont_int _ (hG.comp (f := fun q : (A × V) × V => (q.1.1, q.1.2, q.2)) (by fun_prop))
    exact h.integral_prod_left
  rw [integral_integral_swap h1]
  refine integral_congr_ae (ae_of_all _ fun v₁ => ?_)
  refine integral_integral_swap ?_
  exact cont_int _ (hG.comp (f := fun q : A × V => (q.1, v₁, q.2)) (by fun_prop))

theorem UpperTheory.leviInducedSection_fixed_by_archIdempotent_and_level :
    ∀ {K : Type} [Field K] [NumberField K] (ρ : Measure (KG K 2)), IsProbabilityMeasure ρ → ∀ Ψ : G1 K (2 + 2) → ℂ, (Continuous fun k : KG K (2 + 2) => Ψ k) → ∀ φ₁ φ₂ : G1 K 2 → ℂ, Continuous φ₁ → Continuous φ₂ → (∃ B : ℝ, ∀ m, ‖φ₁ m‖ ≤ B) → (∃ B : ℝ, ∀ m, ‖φ₂ m‖ ≤ B) → ∀ f : G1 K (2 + 2) → ℂ, (∀ X m₁ m₂ t, ∀ k ∈ KG K (2 + 2), f (nn X * lv m₁ m₂ t * k) = ∫ v₁ : KG K 2, ∫ v₂ : KG K 2, Ψ (lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 * k) * φ₁ (m₁ * (v₁ : G1 K 2)⁻¹) * φ₂ (m₂ * (v₂ : G1 K 2)⁻¹) ∂ρ ∂ρ) → (∀ (κ : Measure (archCompact K (2 + 2))) (e : archCompact K (2 + 2) → ℂ), IdemA κ e → (∀ k ∈ KG K (2 + 2), ∫ a, e a * Ψ (k * arc1 a) ∂κ = Ψ k) → FixA κ e f) ∧ ∀ U : Subgroup (FA K (2 + 2)), U ≤ AdelicGLn.integralFiniteGL K (2 + 2) → (∀ k ∈ KG K (2 + 2), ∀ u ∈ U, Ψ (k * fin1 u) = Ψ k) → FixF U f := by
  intro K _ _ ρ hρ Ψ hΨ φ₁ φ₂ h₁ h₂ _ _ f hf
  obtain ⟨-, -, -, hlvc, -, -, -, -, -, -, hlvK, hcomp⟩ := blkLaws (K := K)
  obtain ⟨α, β, -, -, -, -, harc, hfin⟩ := UpperTheory.maximalCompact_unique_arch_finite_decomposition (K := K) (2 + 2)
  haveI : CompactSpace (KG K 2) := isCompact_iff_compactSpace.1 (hcomp 2).1
  refine ⟨fun κ e he hfix g => ?_, fun U hU hfix u hu g => ?_⟩
  · haveI := he.haar.prob
    obtain ⟨X, m₁, m₂, t, k, hk, rfl⟩ := iwa g
    have harc1 : Continuous fun a : archCompact K (2 + 2) => arc1 a :=
      continuous_archP.comp continuous_subtype_val
    have hfa : ∀ a : archCompact K (2 + 2), e a * f (nn X * lv m₁ m₂ t * k * arc1 a) =
        ∫ v₁ : KG K 2, ∫ v₂ : KG K 2, e a * (Ψ (lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 * (k * arc1 a)) *
          φ₁ (m₁ * (v₁ : G1 K 2)⁻¹) * φ₂ (m₂ * (v₂ : G1 K 2)⁻¹)) ∂ρ ∂ρ := by
      intro a
      rw [mul_assoc (nn X * lv m₁ m₂ t) k, hf X m₁ m₂ t _ (mul_mem hk (harc a)), ← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun v₁ => ?_)
      beta_reduce
      rw [← integral_const_mul]
    have hlv : Continuous fun p : archCompact K (2 + 2) × KG K 2 × KG K 2 =>
        lv (p.2.1 : G1 K 2) (p.2.2 : G1 K 2) 0 :=
      hlvc.comp (f := fun p : archCompact K (2 + 2) × KG K 2 × KG K 2 =>
        ((p.2.1 : G1 K 2), (p.2.2 : G1 K 2), (0 : ℝ))) (by fun_prop)
    have hpsi : Continuous fun p : archCompact K (2 + 2) × KG K 2 × KG K 2 =>
        Ψ (lv (p.2.1 : G1 K 2) (p.2.2 : G1 K 2) 0 * (k * arc1 p.1)) :=
      hΨ.comp (Continuous.subtype_mk (hlv.mul (continuous_const.mul (harc1.comp continuous_fst)))
        fun p => mul_mem (hlvK _ p.2.1.2 _ p.2.2.2) (mul_mem hk (harc p.1)))
    have hc₁ : Continuous fun p : archCompact K (2 + 2) × KG K 2 × KG K 2 =>
        φ₁ (m₁ * (p.2.1 : G1 K 2)⁻¹) :=
      h₁.comp (continuous_const.mul (by fun_prop))
    have hc₂ : Continuous fun p : archCompact K (2 + 2) × KG K 2 × KG K 2 =>
        φ₂ (m₂ * (p.2.2 : G1 K 2)⁻¹) :=
      h₂.comp (continuous_const.mul (by fun_prop))
    have he' : Continuous fun p : archCompact K (2 + 2) × KG K 2 × KG K 2 => e p.1 :=
      he.cont.comp continuous_fst
    simp_rw [hfa]
    rw [swap3 κ ρ (fun a v₁ v₂ => e a * (Ψ (lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 * (k * arc1 a)) *
      φ₁ (m₁ * (v₁ : G1 K 2)⁻¹) * φ₂ (m₂ * (v₂ : G1 K 2)⁻¹))) (he'.mul ((hpsi.mul hc₁).mul hc₂)),
      hf X m₁ m₂ t k hk]
    refine integral_congr_ae (ae_of_all _ fun v₁ => integral_congr_ae (ae_of_all _ fun v₂ => ?_))
    have hfx := hfix _ (mul_mem (hlvK _ v₁.2 _ v₂.2) hk)
    have hsplit : ∀ a : archCompact K (2 + 2), e a * (Ψ (lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 * (k * arc1 a)) *
        φ₁ (m₁ * (v₁ : G1 K 2)⁻¹) * φ₂ (m₂ * (v₂ : G1 K 2)⁻¹)) =
        e a * Ψ (lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 * k * arc1 a) *
          (φ₁ (m₁ * (v₁ : G1 K 2)⁻¹) * φ₂ (m₂ * (v₂ : G1 K 2)⁻¹)) := by
      intro a
      rw [← mul_assoc (lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0) k]
      ring
    show ∫ a, e a * (Ψ (lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 * (k * arc1 a)) *
        φ₁ (m₁ * (v₁ : G1 K 2)⁻¹) * φ₂ (m₂ * (v₂ : G1 K 2)⁻¹)) ∂κ = _
    simp_rw [hsplit]
    rw [integral_mul_const, hfx, mul_assoc]
  · obtain ⟨X, m₁, m₂, t, k, hk, rfl⟩ := iwa g
    have hu' : fin1 u ∈ KG K (2 + 2) := hfin ⟨u, hU hu⟩
    rw [mul_assoc (nn X * lv m₁ m₂ t) k, hf X m₁ m₂ t _ (mul_mem hk hu'), hf X m₁ m₂ t k hk]
    refine integral_congr_ae (ae_of_all _ fun v₁ => integral_congr_ae (ae_of_all _ fun v₂ => ?_))
    show Ψ (lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 * (k * fin1 u)) * _ * _ = Ψ (lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 * k) * _ * _
    rw [← mul_assoc, hfix _ (mul_mem (hlvK _ v₁.2 _ v₂.2) hk) u hu]
