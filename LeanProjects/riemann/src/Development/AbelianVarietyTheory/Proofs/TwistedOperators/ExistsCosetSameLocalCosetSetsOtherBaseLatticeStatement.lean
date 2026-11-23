import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetSameLocalCosetSetsOtherBaseLattice
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coset_same_localCosetSets_other_baseLattice : ∀ {D : D7} {T T' : Type} {L : LevCh D T} {L' : LevCh D T'} {sc : Consts} (G : GridData L sc) (G' : GridData L' sc)
    (B : GlobalTheory.FunObj.Frames G) (B' : GlobalTheory.FunObj.Frames G'),
    IsSDFrame (Yc D 0) (L.βY 0) (L.ΛY 0) (D.host.g 0 * D.host.g 1) →
    IsSDFrame (Yc D 0) (L'.βY 0) (L'.ΛY 0) (D.host.g 0 * D.host.g 1) →
    G'.pl.v0 = G.pl.v0 → G'.pl.w = G.pl.w → G'.sp.Vs 1 0 = G.sp.Vs 1 0 → HEq (B'.βs 1 0) (B.βs 1 0) →
    ∀ (h : 0 < D.R.m) (κ' : G'.CosAt 0), ∃ κ : G.CosAt 0, ∀ (t : T') (t₀ : T) (w : Pl D.host.E),
      GlobalTheory.FunObj.cosetSet t w B' h κ' = GlobalTheory.FunObj.cosetSet t₀ w B h κ := by
  first | exact @GlobalTheory.FunObj.CosFlip.exists_cos_cosetSet_eq | exact GlobalTheory.FunObj.CosFlip.exists_cos_cosetSet_eq | (intros; apply GlobalTheory.FunObj.CosFlip.exists_cos_cosetSet_eq <;> assumption)
