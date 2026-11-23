import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfRunTh
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.MuVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistDiscreteCsd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterThetaInvariantExponent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGoodConjSelfDualTwistSplitUnramified

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.muInf :
    MuInf := by
  intro E _ _ _ μ e hμ
  refine ⟨fun w hw => ?_, fun N k P v => ⟨?_, ?_⟩⟩
  · simpa using UpperTheory.HeckeLevelFrameExistence.muVal E μ e hμ w hw 1
  · rw [((ParLaws.hasInfChar_infChar P v.embedding).twist (μ ^ k)).infChar_eq]
    refine Multiset.map_congr rfl fun z _ => ?_
    rw [GlobalTheory.BCT.TwistDisc.expo_pow, GlobalTheory.BCT.MuProps.expo_emb hμ]
    ring
  · rw [((ParLaws.hasInfChar_infChar P (ComplexEmbedding.conjugate v.embedding)).twist (μ ^ k)).infChar_eq]
    refine Multiset.map_congr rfl fun z _ => ?_
    rw [GlobalTheory.BCT.TwistDisc.expo_pow, GlobalTheory.BCT.MuProps.expo_conj hμ]
    ring
