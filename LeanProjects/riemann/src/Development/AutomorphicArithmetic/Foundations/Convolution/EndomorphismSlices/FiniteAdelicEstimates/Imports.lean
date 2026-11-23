import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.HeckeComponentVectors.HeckeFixedSplitPlace
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.HeckeComponentVectors.TjZeroAct
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.HeckeComponentVectors.HeckeVecFst
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.HeckeComponentVectors.SatakeConjugateInverse

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.F.RS

attribute [local instance] borelG borelF borelA borelH

theorem UpperTheory.Zero.ConvolutionTheory.EB.satRead₁ :
    UpperTheory.Zero.ConvolutionTheory.EB.SatRead₁ := by
  intro E _ _ _ a b l₁ l₂ D A S Z L hS hZ f hf _ hL _ w hw hwZ t ht
  have h := hkAct E a b l₁ l₂ D A S Z L hS hZ f hL w hw hwZ
  obtain ⟨B₁, B₂, h1, h2, h3, h4⟩ := sat2Ex E a b w _ _ (pairRt a b w) f t hf (fun i => (h 0 i).1.1)
    fun p i => ((h p i).1.2).symm.trans (congrFun (ht p) i)
  refine ⟨B₁, B₂, h1, h2, h3, ?_, ?_⟩
  · rintro φ ⟨i, m, e⟩
    exact (sat2Slice E a b w _ _ _ (h4 i)).1 φ m e
  · rintro φ ⟨i, m, e⟩
    exact (sat2Slice E a b w _ _ _ (h4 i)).2 φ m e
