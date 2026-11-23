import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SplitEig
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ContinuousPrN
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.DiagInvVal

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.meanLaws :
    MeanLaws := by
  intro E _ _ N Ψ hΨ
  have hgl : Continuous (gl : G1 E → GL (Fin 2) (A E)) := by fun_prop
  haveI : IsFiniteMeasure (N.μ.restrict N.D) := ⟨by simpa using volE E N⟩
  have hc : ∀ y, Continuous fun h : G1 E => Ψ (gl h * y) := fun y =>
    hΨ.cont.comp (hgl.mul continuous_const)
  have hL : ∀ y, UpperTheory.ConvolutionTheory.R2.Ff.LRat fun x => Ψ (x * y) := fun y γ g => by
    simpa only [mul_assoc] using hΨ.left γ (g * y)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨B, hB⟩ := hΨ.bdd {y} isCompact_singleton
    exact Integrable.of_bound (hc y).aestronglyMeasurable B
      (Eventually.of_forall fun h => hB h y rfl)
  · rw [continuous_iff_continuousAt]
    intro y
    obtain ⟨C, hCc, hCn⟩ := exists_compact_mem_nhds y
    obtain ⟨B, hB⟩ := hΨ.bdd C hCc
    refine continuousAt_of_dominated (bound := fun _ => B) ?_ ?_ (integrable_const B) ?_
    · exact Eventually.of_forall fun z => (hc z).aestronglyMeasurable
    · filter_upwards [hCn] with z hz
      exact Eventually.of_forall fun h => hB h z hz
    · exact Eventually.of_forall fun h =>
        (hΨ.cont.comp (continuous_const.mul continuous_id)).continuousAt
  · intro h y
    simpa only [mul_assoc] using ((invE E N).2 _ (hL y)).1 h
  · intro γ y
    simpa only [mul_assoc] using ((invE E N).2 _ (hL y)).2 γ
