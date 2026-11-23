import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.KkCpt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.BorHomeo
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Iwa

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.iwa :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], Iwa F := by
  intro F _ _ _
  obtain ⟨hK, hKc⟩ := M.kkCpt F
  obtain ⟨hB, e, he⟩ := M.borHomeo F
  refine ⟨hKc, fun C hC => ?_⟩
  have hemb : IsClosedEmbedding (Subtype.val : M.Bor F → G1 F) := hB.isClosedEmbedding_subtypeVal
  have hS : IsCompact ((fun p : G1 F × G1 F => p.1 * p.2) '' (C ×ˢ KK F)) :=
    (hC.prod hKc).image continuous_mul
  refine ⟨Prod.fst '' (e.symm '' ((Subtype.val : M.Bor F → G1 F) ⁻¹'
    ((fun p : G1 F × G1 F => p.1 * p.2) '' (C ×ˢ KK F)))),
    ((hemb.isCompact_preimage hS).image e.symm.continuous).image continuous_fst, fun g hg => ?_⟩
  obtain ⟨b, a, k, hk, rfl⟩ := M.iwa F g
  refine ⟨b, a, ?_, k, hk, rfl⟩
  refine ⟨(a, b), ⟨e (a, b), ?_, e.symm_apply_apply _⟩, rfl⟩
  change ((e (a, b) : M.Bor F) : G1 F) ∈ (fun p : G1 F × G1 F => p.1 * p.2) '' (C ×ˢ KK F)
  rw [he]
  refine ⟨(nU b * mD a * k, k⁻¹), ⟨hg, ?_⟩, by simp⟩
  change k⁻¹ ∈ KK F
  rw [hK] at hk ⊢
  exact (M.Ks F).inv_mem hk
