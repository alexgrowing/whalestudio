import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.GaussBinomialTwistedSumIdentity
import Development.AutomorphicSpectrum.Definitions.TwistedFlags.ReachOrth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnramifiedCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars (EigSys badPl IsIP IsUp IsUpTop topStep IsLValue)
open GlobalTheory.LFun (Fam twist segFam seg val above IsCont Bounded IsSysParamD IsParamFunV UnrAt)
open GlobalTheory.CompanionTheory.OntoAll
open GlobalTheory.Hk3 GlobalTheory.CompanionTheory.Ipf.Aut
open GlobalTheory.Chain (ChainPar IsStepWeil IsVacVec ptOf expS expT)
open GlobalTheory.PairLift (Inputs RulePar)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussBinomial_twisted_sum_identity : ∀ {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a t k : ℕ) (B : Multiset ℂˣ) (x y : ℂˣ), B.card = a → k ≤ a + t → ∑ j ∈ Finset.range (min k a + 1), ((Ideal.absNorm w.asIdeal : ℂ) ^ ((a - j) * (k - j)) * (Formalism.L2.Col.gaussBin (Ideal.absNorm w.asIdeal) t (k - j) : ℂ) * ((x : ℂ) * ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℂ) ^ a)⁻¹) ^ k * (((y : ℂ))⁻¹ * (Real.sqrt (Ideal.absNorm w.asIdeal) : ℂ) ^ (a + t)) ^ j) * GlobalTheory.LFun.satEig (Ideal.absNorm w.asIdeal) a B j = GlobalTheory.LFun.satEig (Ideal.absNorm w.asIdeal) (a + t) (B.map (x * y⁻¹ * ·) + seg w x t) k := by
  first | exact @GlobalTheory.CompanionTheory.Ipf.Aut.satEig_twist_add_seg | exact GlobalTheory.CompanionTheory.Ipf.Aut.satEig_twist_add_seg | (intros; apply GlobalTheory.CompanionTheory.Ipf.Aut.satEig_twist_add_seg <;> assumption)
