import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.PTranslAd
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.GlobalHarmonicExistence.InvolutionIntegrals.IntegralCompInvol
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairInvolutionContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSrcMemOrb

open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8

private theorem conj_of_central {G : Type} [Group G] (a b : G) (h : a⁻¹ * b ∈ Subgroup.center G) (t : G) :
    b * t * b⁻¹ = a * t * a⁻¹ := by
  have hc := Subgroup.mem_center_iff.mp h t
  calc b * t * b⁻¹ = a * ((a⁻¹ * b) * t) * (a⁻¹ * b)⁻¹ * a⁻¹ := by group
    _ = a * (t * (a⁻¹ * b)) * (a⁻¹ * b)⁻¹ * a⁻¹ := by rw [hc]
    _ = a * t * a⁻¹ := by group

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.translF_pf :
    TranslF := by
  intro E _ _ _ n u hu
  have hz : (ratF E n u)⁻¹ * PhiU n (Af E) ∈ Subgroup.center (GL (Fin n) (Af E)) := by
    have h := GeneralLinearGroup.map_center_le (algebraMap E (Af E)) (translad_central E n u hu)
    rw [Subgroup.mem_comap, map_mul, map_inv, translad_map_PhiU] at h
    exact h
  have hc := conj_of_central (ratF E n u) (PhiU n (Af E)) hz
  refine ⟨fun g => ?_, ?_, PhiU n (Af E), ?_, fun g => (hc g).symm⟩
  · rw [← hc, Tw.thetaF_eq]
    exact thetaGL_eq n (Af E) _ g
  · rw [← GlobalTheory.EulerTw.Comm.thF_ratF, hu.1, hu.2, one_mul, map_inv]
  · refine Subgroup.mem_iInf.mpr fun w => ?_
    rw [Subgroup.mem_comap, translad_map_PhiU]
    exact GlobalTheory.ThetaSatake.phiU_mem _ n
