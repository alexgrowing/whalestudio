import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace
open scoped NumberField.AdeleRing

section SlopeTestRemainingChoices

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem archimedean_projection_val (a : archCompact K n) :
    ((arc1 a : G1 K n) : AdelicGLn.AdelicGL K n) = infEmb K n (a : archGroup K n) :=
  congrArg Subtype.val (archProj_of_mem (A := ((a : archGroup K n) : ArchUnits K n))
    (maxCompact_le_normOneGL a.2))

private theorem finite_projection_integral_val (h : AdelicGLn.integralFiniteGL K n) :
    ((fin1 (h : FA K n) : G1 K n) : AdelicGLn.AdelicGL K n) = finEmb K n (h : FA K n) :=
  congrArg Subtype.val (MultiplicityOne.finProj_of_mem (maxCompact_le_normOneGL (finEmb_mem_maxCompact h.2)))

end SlopeTestRemainingChoices

theorem UpperTheory.maximalCompact_unique_arch_finite_decomposition :
    ∀ {K : Type} [Field K] [NumberField K] (n : ℕ), ∃ (α : KG K n → archCompact K n) (β : KG K n → AdelicGLn.integralFiniteGL K n), Continuous α ∧ Continuous β ∧ (∀ k : KG K n, (k : G1 K n) = arc1 (α k) * fin1 (β k : FA K n)) ∧ (∀ (a : archCompact K n) (h : AdelicGLn.integralFiniteGL K n) (k : KG K n), (k : G1 K n) = arc1 a * fin1 (h : FA K n) → α k = a ∧ β k = h) ∧ (∀ a : archCompact K n, arc1 a ∈ KG K n) ∧ ∀ h : AdelicGLn.integralFiniteGL K n, fin1 (h : FA K n) ∈ KG K n := by
  intro K _ _ n
  have hval : Continuous fun k : KG K n => ((k : G1 K n) : AdelicGLn.AdelicGL K n) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hpe : Continuous fun k : KG K n => AdelicGLn.prodEquiv K n ((k : G1 K n) : AdelicGLn.AdelicGL K n) :=
    (AdelicGLn.prodEquiv K n).continuous.comp hval
  refine ⟨fun k => ⟨archPart ((k : G1 K n) : AdelicGLn.AdelicGL K n), archPart_mem_archCompact k.2⟩,
    fun k => ⟨finPart ((k : G1 K n) : AdelicGLn.AdelicGL K n), finPart_mem_integralFiniteGL k.2⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Continuous.subtype_mk ((archEquiv K n).continuous.comp (continuous_fst.comp hpe)) _
  · exact Continuous.subtype_mk (continuous_snd.comp hpe) _
  · intro k
    apply Subtype.ext
    rw [Subgroup.coe_mul, archimedean_projection_val, finite_projection_integral_val]
    exact (infEmb_mul_finEmb _).symm
  · intro a h k hk
    have e : ((k : G1 K n) : AdelicGLn.AdelicGL K n) = infEmb K n (a : archGroup K n) * finEmb K n (h : FA K n) := by
      rw [hk, Subgroup.coe_mul, archimedean_projection_val, finite_projection_integral_val]
    have e' : AdelicGLn.prodEquiv K n ((k : G1 K n) : AdelicGLn.AdelicGL K n) =
        ((archEquiv K n).symm (a : archGroup K n), (h : FA K n)) := by
      rw [e, map_mul, prodEquiv_infEmb, prodEquiv_finEmb]
      simp
    constructor
    · apply Subtype.ext
      change archEquiv K n (AdelicGLn.prodEquiv K n ((k : G1 K n) : AdelicGLn.AdelicGL K n)).1 = _
      rw [e']
      simp
    · apply Subtype.ext
      change (AdelicGLn.prodEquiv K n ((k : G1 K n) : AdelicGLn.AdelicGL K n)).2 = _
      rw [e']
  · intro a
    change ((arc1 a : G1 K n) : AdelicGLn.AdelicGL K n) ∈ Reduction.maxCompact
    rw [archimedean_projection_val]
    exact a.2
  · intro h
    change ((fin1 (h : FA K n) : G1 K n) : AdelicGLn.AdelicGL K n) ∈ Reduction.maxCompact
    rw [finite_projection_integral_val]
    exact finEmb_mem_maxCompact h.2
