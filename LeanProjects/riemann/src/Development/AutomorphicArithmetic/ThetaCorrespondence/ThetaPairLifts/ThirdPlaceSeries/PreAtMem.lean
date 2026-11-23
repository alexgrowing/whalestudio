import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.PreAtMem
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisPreconditions
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartsGive
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemberImp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RamificationJumpsMemAtLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FiniteTriplesSatisfyCondition
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisGoodFTAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BuiltLaws
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameTwistAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OneFieldOfNAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisRepIsGeometricAtAllPlaces
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SParts
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAltAltAlt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisExtra
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ResidualIrreducibleOfTheoremThreePrime
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PrvZrOfInputsRowsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightParamOfPinStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisSide
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreFurther
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisDepthZeroType
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GeometricGaloisRepCompatibility
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AdmissibleResidualTameEigenvalues

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.NPin GlobalTheory.NFacts
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField ReciprocityTheory.Gal GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Fc GlobalTheory.NFacts
noncomputable section
namespace UpperTheory.GalS
structure Core0Alt (D : D7) : Prop where
  what₂ : _root_.GlobalTheory.NRows.PointConditions' D
  adm : _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D
  Conclusion1 : _root_.Formalism.MainNotions.SumRepresentations.provisionFirst D
  z : SumRepresentations.ConclusionZ D
  rhoBar : ResidualIrreducibleRankR D
  g3p : _root_.UpperTheory.GalS.AdmissibleResidualTameEigenvalues D
  weight : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.WeightParam D
  block : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.BlockCharParam D
  muUnr : GlobalTheory.HubX.MuUnr D
  depthG : GlobalTheory.HubX.DepthZeroG D
  bc : SphericalInertData.Conclusion1 D
  lam : GlobalTheory.NRows.LamUsed D
theorem core0_of_local_duality_inputs : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DepthZeroSupport → LocalFiniteness → LocalTateDuality → LocalEulerChar →
    ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7), _root_.GlobalTheory.NRows.LinkedInputs hL D → JumpsCard D.nd D.naut → _root_.UpperTheory.GalS.Core0Alt D := by
  intro hP hc hd hs hF hT hE hL D I hJ
  have R : _root_.GlobalTheory.NRows.PointConditions' D := _root_.GlobalTheory.T.theta_conditions_of_inputs_of_jumpsCard hP hc hd hL D I hJ
  have at' : _root_.Formalism.MainNotions.SumRepresentations.AdmAtAlt D := I.admAt R.a R.b
  have p1 : _root_.Formalism.MainNotions.SumRepresentations.provisionFirst D := I.Conclusion1 (_root_.UpperTheory.GalS.Parts.main_alt_alt D) R.a R.b
  have g3 : _root_.UpperTheory.GalS.AdmissibleResidualTameEigenvalues D :=
    _root_.GlobalTheory.AdmTame.main_alt_alt_alt D R.a.tie0 R.a.a2 R.a.a5 (_root_.GlobalTheory.TieLabAt.main_alt_alt hL D I.P).2.1
  have rb : ResidualIrreducibleRankR D :=
    _root_.Formalism.MainNotions.AdmissibleThreePrime.residual_irreducible_of_theorem_three_prime_alt D ⟨R.a.tieLab, g3⟩ R.a.a5 (GlobalTheory.BrauerNesbittIrr.litBNIrr _) R.c.rho R.c.dz
  have adm : _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D := ⟨at', (residualIrreducibility_forms_equivalent D).2 rb, I.isot⟩
  have z : SumRepresentations.ConclusionZ D := (SumRepresentations.multiplicity_statement_iff_reduced D I.isot p1.2.2).2 (_root_.GlobalTheory.T.reducedMultiplicity_of_inputs hL D I R)
  have wt : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.WeightParam D := _root_.GlobalTheory.T.weight_param_of_character_choice hL D I.P
  have bl : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.BlockCharParam D := GlobalTheory.BlockCharInf.main D I.P.cf I.P.C I.P.tp I.P.chr
  have rm : ∀ i : D.nd.Loc, Nonempty (RowMod D I.P.rep (D.nd.j i)) := fun i => by
    have hj := D.nd.j_range i
    obtain ⟨Y, -⟩ := _root_.GlobalTheory.RowModCanon.main_alt_alt hc hd hL D I.P I.X I.agree ⟨D.nd.j i - 1, by omega⟩ (D.nd.j i)
      (by simp only; omega)
    exact ⟨Y⟩
  exact
    { what₂ := R
      adm := adm
      Conclusion1 := p1
      z := z
      rhoBar := rb
      g3p := g3
      weight := wt
      block := bl
      muUnr := _root_.GlobalTheory.MuUnrTie.main_alt_alt hP.fin hL D I.P
      depthG := _root_.GlobalTheory.T.depthZeroG_of_rowMod hP hs hL D I.P rm
      bc := I.bc
      lam := I.lam }
theorem galois_preconditions_at_mem : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → SerN → GlobalTheory.Published.DepthZeroSupport → LocalFiniteness →
    LocalTateDuality → LocalEulerChar → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists,
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ nch _ _ => _root_.UpperTheory.GalC.GaloisPreconditions (w.D Z) nch := by
  intro prn prx ser dzs lf ltd lec hL
  have hA := _root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.NRows.AtLayer.exists_inputs_pinAt_jumpsCard_at_mem prn prx hL)
    (_root_.GlobalTheory.HeightCounting.Up.TripFin.finiteTriples_satisfy_condition_alt prn ser hL)) (_root_.GlobalTheory.T.goodFTAll_at_mem_of_inputs prn hL)
  refine EvG.imp hA fun _ _ _ _ _ hK => large₂.imp hK fun B f T _ H kp w Z Wt p0 t nch n xd c hne hrx cp => ?_
  obtain ⟨⟨⟨I, -, jumps⟩, trip⟩, good⟩ := H kp w Z Wt p0 t nch n xd c hne hrx cp
  obtain ⟨ne⟩ := hne
  have core : _root_.UpperTheory.GalS.Core0Alt (w.D Z) := _root_.UpperTheory.GalS.core0_of_local_duality_inputs prn.what₂ prn.hc prn.decay dzs lf ltd lec hL (w.D Z) I jumps
  have large : GlobalTheory.CoefDuty.Large (w.D Z) := ne.large
  exact { core with
    c2 := _root_.GlobalTheory.LocCoincide.main_alt_alt hL (w.D Z) I.P.M c.a.nt.toNBuilt I.P.H.hecke
    large := large
    nct := n.tie
    trip := trip
    same := _root_.GlobalTheory.HeightCounting.SameTw.sameTwist_at_alt hL (w.D Z) _ nch _ c.a (_root_.GlobalTheory.NFacts.AtMemFacts.oneField_of_nAt_alt c.a)
    good := good }
end UpperTheory.GalS
end
end
