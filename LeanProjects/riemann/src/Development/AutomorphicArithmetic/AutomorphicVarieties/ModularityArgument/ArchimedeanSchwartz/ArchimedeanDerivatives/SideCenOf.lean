import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.GenericFunctionalEquation.GenFE

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.HenQ Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.GJStandardL GroundTheory.Automorphic.GodementJacquet
open GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.GJStandardLCuspidal UpperTheory.V UpperTheory.V.Z.Inf

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

private theorem far_ne {A : ℂ → ℂ} (hA : Differentiable ℂ A) (h0 : A ≠ 0) (c : ℝ) : ∃ s : ℂ, c < s.re ∧ A s ≠ 0 := by
  by_contra h
  push Not at h
  refine h0 (funext fun x => AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (hA.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (Set.mem_univ ((c + 1 : ℝ) : ℂ)) ?_ trivial)
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show c < ((c + 1 : ℝ) : ℂ).re by simp)] with s hs using h s hs
