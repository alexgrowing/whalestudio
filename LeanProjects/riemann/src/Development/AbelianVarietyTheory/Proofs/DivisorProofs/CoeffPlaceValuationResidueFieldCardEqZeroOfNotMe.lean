import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFlatIntegrand
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralUnfoldingVariablesMemFieldRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemVarLat
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.VwEqZeroOfNotMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.UnfoldLoss.ResCardAway

theorem absNorm_eq_plc_pow {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) :
    ∃ n : ℕ, Ideal.absNorm P.asIdeal = ringChar (𝓞 K ⧸ P.asIdeal) ^ n := by
  classical
  haveI : P.asIdeal.IsMaximal := P.isMaximal
  letI : Field (𝓞 K ⧸ P.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 K ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  letI : Fintype (𝓞 K ⧸ P.asIdeal) := Fintype.ofFinite _
  obtain ⟨n, -, hn⟩ := FiniteField.card (𝓞 K ⧸ P.asIdeal) (ringChar (𝓞 K ⧸ P.asIdeal))
  refine ⟨n, ?_⟩
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  exact hn

theorem vw_resCard_eq_zero : ∀ {D : D7} (P : Pl D.host.E) (w : PlL D),
    ((Formalism.EigenvalueLevelCeiling.plc P : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal →
    vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) = 0 := by
  intro D P w h
  obtain ⟨n, hn⟩ := absNorm_eq_plc_pow P
  have hq : resCard (Kw P) = Formalism.EigenvalueLevelCeiling.plc P ^ n :=
    (ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.ResCardPlace.resCard_Kw P).trans hn
  have hnot : ((resCard (Kw P) : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal := by
    rw [hq, Nat.cast_pow]
    exact fun hm => h (w.isPrime.mem_of_pow_mem n hm)
  letI : StarRing D.what₂.LL := starRingOfComm
  have := Formalism.DivisionValues.ValuationZeroReduction.vw_eq_zero_of_not_mem w _ hnot
  simpa using this

end GlobalTheory.UnfoldLoss.ResCardAway
