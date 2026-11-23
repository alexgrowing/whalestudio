import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.NAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.NIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.SvSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CobTail
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CobLaws

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.nInt :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (N : W →ₗ[ℂ] V), M.IsN N → ∀ (Y : H →L[ℂ] H) (β : ℝ → V →L[ℂ] V) (β' : ℝ → W →L[ℂ] W), Ker β → Ker β' → M.Acts Y β β' →
      ∀ w, N (symb β' 0 w) = symb β 0 (N w) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M N hN Y β β' k1 k2 ha w
  obtain ⟨-, cadd, -, -, -, -, -, cmap⟩ := cobLaws M.F
  have hY : ∀ t h, Y (M.F.U t h) = M.F.U t (Y h) := fun t h => by
    obtain ⟨u, rfl⟩ := M.J.surjective h
    rw [M.hJ, ha.1, ha.1, M.hJ]
    exact congrArg M.J (DFunLike.congr_fun ((convLaws β k1).1 t) u)
  have h1 := cmap M.F Y hY _ (hN w)
  rw [map_sub, ha.1, ha.2] at h1
  obtain ⟨-, b1, s1⟩ := (svSpec (V := W)).2 w
  obtain ⟨-, b2, s2⟩ := (svSpec (V := V)).2 (N w)
  obtain ⟨b3, s3⟩ := (convLaws β' k2).2.2 _ b1
  obtain ⟨b4, s4⟩ := (convLaws β k1).2.2 _ b2
  have h2 := nAll M N hN _ b3
  rw [s3, s1] at h2
  have h3 := ((cobTail _).2 ((cobTail _).1 b4)).2
  rw [s4, s2] at h3
  have h4 := (cobLaws (shF V)).2.2.2.2.2.2.2 M.F (M.J.toContinuousLinearEquiv : L V →L[ℂ] H) (fun t h => (M.hJ t h).symm) _ h3
  have h5 := (cadd _ _ (cadd _ _ h1 h2).2 h4).1
  have h6 : M.F.Cob (M.J (one V (N (symb β' 0 w) - symb β 0 (N w)))) := by
    convert h5 using 1
    simp
  exact sub_eq_zero.1 ((nIso M).1 _ h6)
