import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CobTail
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CobLaws

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.nAll :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (N : W →ₗ[ℂ] V), M.IsN N → ∀ p : L W, Bdd p → M.F.Cob (M.J' p - M.J (one V (N (∫ x, p x)))) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M N hN p hp
  obtain ⟨h1, h2⟩ := cobTail p
  have h3 := (h2 (h1 hp)).2
  have h4 := (cobLaws (shF W)).2.2.2.2.2.2.2 M.F.rev (M.J'.toContinuousLinearEquiv : L W →L[ℂ] H) (fun t h => by
    show M.J' (sh W t h) = M.F.U (-t) (M.J' h)
    rw [M.hJ', neg_neg]) _ h3
  have h5 := ((cobLaws M.F).2.2.2.1 _).1 h4
  have h6 := ((cobLaws M.F).2.1 _ _ h5 (hN (∫ x, p x))).1
  convert h6 using 1
  simp
