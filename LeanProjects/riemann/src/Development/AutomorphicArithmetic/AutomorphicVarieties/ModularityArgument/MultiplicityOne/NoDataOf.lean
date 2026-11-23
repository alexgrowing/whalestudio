import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.RIdent
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.IsDecOfGlobLev
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.RCountAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.ContinuousESp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.CpUniq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.GeomTr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.RelIndexGlobNe
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.LevInd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.LcLev
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.ChoiceM
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.OffSec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfPi

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.G UpperTheory.V.Z.Tf.GOne UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GaloisFromTraceFormula

namespace UpperTheory.V.Z.Mult

theorem noData_of (hW : GalWeak 4) : NoData := by
  intro E _ _ _ hunr n hn1 hn4 π hreg hd D₁ h1 h2 h3 h4
  obtain ⟨D, r, t, s, hno⟩ := preOf (partNorm absInf) csdSat Asm.places E n hn1 π hd D₁ h1 h2 h3 h4
  obtain ⟨D₀, hone, hr⟩ := onePre E n hn1 π hreg (csdDisc E n hn1 π hd)
  have hs := oneSat E n hn1 π D₀ hone
  have ht : D₀.ThetaStable := (csdSat E n hn1 π hd).mono fun w ⟨B, a, b⟩ => ⟨B, (hs w B).1 a, fun u hu => (hs u _).1 (b u hu)⟩
  obtain ⟨e, he⟩ := Rig.locRigid_holds E n D D₀ r hr (galStep_le hW E hunr n hn4 D D₀ r hr t ht
    (s.mono fun w hw hx => (hw hx).imp fun B hB => ⟨hB.1, (hs w B).1 hB.2⟩))
  exact absurd (onlyOne cuspOrTwo notTwo oneSat E n hn1 π D D₀ e r hone he) hno

theorem mult_of (hW : GalWeak 4) (hC : CompOf) (hS : StableBlockSA) : Mult :=
  have hA := rCountAt hC evalD cpUniq Asm.places
  rMult (rIdent (noData_of hW) hA geomTr UpperTheory.ConvolutionTheory.G2.g2s UpperTheory.ConvolutionTheory.G2.matchUnit UpperTheory.ConvolutionTheory.G2.matchSplit
      (endoS (enlarge Th.stUnit hecke_eigenvalues_unitary_one_factor unitary_one_characters_separated_by_eigenvalues Asm.places) Asm.places (UpperTheory.Zero.ConvolutionTheory.EB.endoBlockG cuspReadI)) hS)
    hA levTr geomTr levInd lcLev choiceM offSec muEx

end UpperTheory.V.Z.Mult
