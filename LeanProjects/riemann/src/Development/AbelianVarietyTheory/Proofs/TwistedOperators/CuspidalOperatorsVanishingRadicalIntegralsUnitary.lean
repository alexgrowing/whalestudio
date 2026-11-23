import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompOfIsTraceClass
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableDescendOrbitSum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralNormRmulLe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAutomorphicConvolutionMemCuspidalOfRadicaStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumCuspidalMultiplicityTraceStatement

noncomputable section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Cusp GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed

namespace GlobalTheory.CuspidalOpAssembly

section Compress

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem trace_comp_comp_of_comp_eq_id (S : K →L[ℂ] H) (P : H →L[ℂ] K) (hPS : ∀ y, P (S y) = y)
    {T : K →L[ℂ] K} (hT : IsTraceClass T) : trace (S ∘L T ∘L P) = trace T := by
  obtain ⟨n, B, C, hB, hC, rfl⟩ := hT
  have e : S ∘L (∑ i, B i ∘L C i) ∘L P = ∑ i, (S ∘L B i) ∘L (C i ∘L P) := by
    ext x; simp
  have t : ∀ i, trace ((S ∘L B i) ∘L (C i ∘L P)) = trace (B i ∘L C i) := fun i => by
    rw [trace_comp_comm ((hB i).comp_left S) ((hC i).comp_right P), trace_comp_comm (hB i) (hC i)]
    congr 1
    ext x; simp [hPS]
  have h1 : HasSum (fun j => ⟪stdBasis H j, (S ∘L (∑ i, B i ∘L C i) ∘L P) (stdBasis H j)⟫_ℂ)
      (∑ i, trace (B i ∘L C i)) := by
    rw [e]
    simpa only [ContinuousLinearMap.sum_apply, inner_sum, t] using
      hasSum_sum fun i (_ : i ∈ Finset.univ) =>
        hasSum_trace_comp (stdBasis H) ((hB i).comp_left S) ((hC i).comp_right P)
  have h2 : HasSum (fun j => ⟪stdBasis K j, (∑ i, B i ∘L C i) (stdBasis K j)⟫_ℂ) (∑ i, trace (B i ∘L C i)) := by
    simpa only [ContinuousLinearMap.sum_apply, inner_sum] using
      hasSum_sum fun i (_ : i ∈ Finset.univ) => hasSum_trace_comp (stdBasis K) (hB i) (hC i)
  exact h1.tsum_eq.trans h2.tsum_eq.symm

end Compress

theorem cuspidalOperators : GlobalTheory.Published.CuspTraceClass → ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V))
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant], CuspidalOperators V μ := by
  intro hCT D V μ _ _ f hf h1 h2
  have c := GlobalTheory.Orb.continuous_of_mem_ccAd hf
  have m1 : GlobalTheory.IndefiniteRowSideFullHecke.TraceKernelDecomposition.MapsIntoCusp V μ f := GlobalTheory.T.unitaryAutomorphicConvolution_mem_cuspidal_of_radical_zero D V μ f hf h1
  have m2 : GlobalTheory.IndefiniteRowSideFullHecke.TraceKernelDecomposition.MapsIntoCusp V μ (starFn f) :=
    GlobalTheory.T.unitaryAutomorphicConvolution_mem_cuspidal_of_radical_zero D V μ (starFn f) (GlobalTheory.Orb.starFn_mem_ccAd hf) h2
  have hd := GlobalTheory.CuspSpectrum.traceIsDiagonal (μ := μ) hCT hf m2
  have hk := fun (F : DividedPowerChartLift V μ) (x : GA D V) =>
    GlobalTheory.AutomorphicL2KernelIntegral.convR_eq_integral_kernelQ (GA D V) (GQ V) μ f c.1 c.2 F x
  obtain ⟨t1, t2, t3⟩ := GlobalTheory.T.hasSum_cuspidalMultiplicity_trace hCT D V μ f hf
  have etr : trace (RopG V μ f) = trace (RcuspOp V μ f) := by
    rw [GlobalTheory.TraceDiagonal.RopG_eq_comp c.1 c.2 m2]
    exact trace_comp_comp_of_comp_eq_id _ _
      (fun y => Submodule.orthogonalProjection_mem_subspace_eq_self y) (hCT D V μ f hf)
  refine ⟨m1, fun F hF => ?_, hd.1, fun F p => ?_, fun F => ?_, hd.2.1, hd.2.2, fun c' => ?_, t1, t2, etr ▸ t3⟩
  · rw [GlobalTheory.TraceDiagonal.RopG_eq_comp c.1 c.2 m2]
    simp [Submodule.orthogonalProjection_eq_zero_iff.2 hF]
  · induction p using Quotient.inductionOn with
    | h x => exact (hk F x).1
  · refine ae_quotMeasure_iff.2 ?_
    filter_upwards [(AutomorphicL2Pointwise.lift_Rop_eq_convR (GA D V) (GQ V) μ f
      (c.1.integrable_of_hasCompactSupport c.2) F).2] with x hx
    exact hx.trans (hk F x).2
  · exact GlobalTheory.CuspSpectrum.multIn_L2cusp_lt (GlobalTheory.Published.cuspDiscreteDecomposition_of_traceClass hCT D V μ) c'.rep.isIrr

end GlobalTheory.CuspidalOpAssembly

end
