import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.ActLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ScatOnSpan
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.RopAdj

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.famEx :
    (ForAllC fun _ _ _ μ _ _ _ _ _ _ _ _ A A' => TruncCpt μ A A') → UnitB → UnipotentBlockPairs → PositivityTheory.Rg.Tf.IntegralApplyAeEq.Main → FamEx := by
  intro hC hU hF hM K _ _ _ μ _ μ₂ _ τ₁ τ₂ hp D d d' A A' P hP
  obtain ⟨a, β, β', sm, hk, st, ⟨k, c, -⟩, ⟨k', c', -⟩, u, u'⟩ := hU K μ μ₂ τ₁ τ₂ hp D d d' A A'
  obtain ⟨sh, ca⟩ := hF K μ μ₂ τ₁ τ₂ hp D d d' A A'
  have sa : IsSelfAdjoint (Rop μ a) := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff', UpperTheory.ConvolutionTheory.K.ropAdj, st]
  obtain ⟨N, h1, h2⟩ := scat_on_span hM A.J A'.J P hP sh ca (Rop μ a) β β' k k' u u' sa c c'
    fun T Λ hT hΛ => hC K μ μ₂ τ₁ τ₂ hp D d d' A A' a P Λ T sm hk hP hT hΛ
  refine ⟨N, Module.finrank ℂ (Eu d), ⟨fun f b b' hb hb' => h1 _ b b' hb.1 hb'.1 hb.2.1 hb'.2.1, h2⟩, ?_⟩
  intro Y s s' hs hs' w
  obtain ⟨κ, m1, m2, m3⟩ := (actLaws A.J).2.2.2.2 _ Y β s k c hs
  obtain ⟨κ', n1, n2, n3⟩ := (actLaws A'.J).2.2.2.2 _ Y β' s' k' c' hs'
  have e := h1 _ κ κ' m1 n1 m2 n2 w
  rw [m3, n3, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, h1 _ β β' k k' c c'] at e
  obtain ⟨g, hg⟩ := u.exists_left_inv
  have inv : ∀ x, g (symb β 0 x) = x := fun x => congrArg (fun B : Eu d →L[ℂ] Eu d => B x) hg
  rw [← inv (N _), e, inv]
