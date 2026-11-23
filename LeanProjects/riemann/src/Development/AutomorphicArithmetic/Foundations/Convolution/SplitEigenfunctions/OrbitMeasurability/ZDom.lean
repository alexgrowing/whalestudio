import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.PerCont
import GroundTheory.GlobalFields.TateThesis.IdeleMeasureQuotient

open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.zDom :
    UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.ZDom := by
  intro E _ _
  refine ⟨normOneMeasure_normOneFundamentalDomain_lt_top E,
    measurableSet_normOneFundamentalDomain E, ?_⟩
  have hc : Continuous (fun z : ↥(IdeleGroup.normOneSubgroup E) =>
      ((z : IdeleGroup E) : (A E)ˣ)) := continuous_subtype_val
  refine ⟨_, (isCompact_closure_normOneFundamentalDomain E).image hc, ?_⟩
  intro z hz
  exact ⟨z, subset_closure hz, rfl⟩
