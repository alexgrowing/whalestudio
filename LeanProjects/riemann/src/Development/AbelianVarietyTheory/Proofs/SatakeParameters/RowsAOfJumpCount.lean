import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsobaricCuspidalMultiplicityOneOfTwisted
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsobaricDiscreteSelfDualMultOneOfIsobaricSumMult
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeSplitOneOfCharTied
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuIntOfCharTied
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NoLocalInvariantsEverywhere
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixCharpolySmul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Adm2OfHyp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EWdOfAbove
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodLabelsRankPartParameterCuspidal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsobaricRigidOfPin
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TieAutAndSplit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisCompatibilityOfJumpsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsBisTer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowsAClose

theorem main : GlobalTheory.NRows.Hypotheses₂ → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), JumpsCard D.nd D.naut → GlobalTheory.NRows.RowsA D := by
  intro hP hL D P hJ
  have hlab := GlobalTheory.TieLabAt.main hL D P
  have hrig : IsobaricRigid D.nd D.naut := GlobalTheory.NPin.isobaricRigid_of_pin hP.fin hP.js hL D P
  have han1 := GlobalTheory.RowClose.isobaricCuspidalMultiplicityOne_of_twisted _ _ _ D.nd D.naut hrig
  have han2 := GlobalTheory.SpehRigid.isobaricDiscreteSelfDualMultOne_of_isobaricSumMultOne _ _ _ D.nd D.naut hrig
  have hcheb := GlobalTheory.ChebSplitDense.chebSplit_nd hP.cheb D
  have ha5 : Formalism.MainNotions.SumRepresentations.adm5 D := (Formalism.MainNotions.SumRepresentations.condition_iff_additive_maps D).2 ⟨han1, han2, fun Sg hSg => by
    have hd := (hcheb hSg.toFinset).closure_eq
    convert hd using 4 with σ
    simp [Set.Finite.mem_toFinset]⟩
  have haut := GlobalTheory.AutomorphismSplitting.tieAut_and_split hP.fin hL D P
  have htie0 : Formalism.MainNotions.SumRepresentations.tie0 D :=
    ⟨GlobalTheory.RowTieLP.main D P.T, haut.1, GlobalTheory.T.galois_compatibility_of_jumps hP.berger hL D P hJ⟩
  have ha2 : Formalism.MainNotions.SumRepresentations.adm2 D := GlobalTheory.GalClose.main hP hL D P
  have ha7 : Formalism.MainNotions.SumRepresentations.adm7 D := GlobalTheory.TempGal.main hP.fin hP.gal hL D P
  have heig := GlobalTheory.EigConcrete.main hP.berger hL D P
  refine ⟨hlab.1, GlobalTheory.RowClose.heckeSplitOne_of_charTied D P.cf P.C P.tp P.chr, htie0, ha2, han1, han2, ha5, ha7,
    GlobalTheory.LocalInvEta.noLocalInvariants_everywhere D P.T htie0 ha2 ha5 ha7
      (GlobalTheory.MuIntegral.muInt_of_charTied D P.cf P.C P.tp P.chr) (GlobalTheory.GoodCuspPoint.main D hlab.1) heig.1 heig.2,
    haut.2⟩

end GlobalTheory.RowsAClose
