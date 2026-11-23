import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.EigenSplitStrings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTransferPosDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeHermitianPairing
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixed
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsFinCombSingleZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactActsOnRealVacuaByDetPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepMemSm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SignEquivInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandRightInvariantSecondFixedLeve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableComplementSecondPolynomial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySatakeWeylInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricFunctionInverseInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesHarishChandra
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharExponentOfInfinityTypeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMultMapRightTranslateFiniteAdelicNormalizer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitDetRowOfGaloisRow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjugateDualTwistByTwistOfConjSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobPolyOfRecTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompNormEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatakeOfIsLocComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicRepIsobaricDecomposition
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsParamDefinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinGLMemOfPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitaryOfIsCsd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaChrTied
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalFamilyOrthogonalDecomposition
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharEqOfSplitOfTied
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeFockMapExistsOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFamilyIffRationalHecke
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoefficientVacuaUnramifiedPlace

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PtString

open GlobalTheory.SphPar GlobalTheory.SphGal GlobalTheory.Hk3 GlobalTheory.CuspRep GlobalTheory.IndefiniteRowSideFullHecke.EigenSplitStrings Formalism.UG Polynomial
open Formalism.MainNotions.SchurIrreducible (IsSplit)

variable {D : D7}

theorem isSplit_iff_conj (P : HeightOneSpectrum (𝓞 D.host.E)) :
    IsSplit (E := D.host.E) (P.under (𝓞 D.host.F)) ↔ Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ≠ P.asIdeal := by
  rw [GlobalTheory.LFun.isSplit_iff, Formalism.DivisionValues.GluingInclusion.conjIdeal_eq]
  constructor
  · rintro ⟨w, w', hne, h, h'⟩ e
    have e' : Formalism.DivisionValues.conjPl P = P := HeightOneSpectrum.ext e
    have a := GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq h
    have b := GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq h'
    rw [e', or_self] at a b
    exact hne (a.trans b.symm)
  · intro h
    exact ⟨P, Formalism.DivisionValues.conjPl P, fun e => h (congrArg HeightOneSpectrum.asIdeal e).symm, rfl,
      (GlobalTheory.LevelPlaces.under_eq_of_isConjPl (GlobalTheory.GoodPrimes.isConjPl_iff.2 rfl)).symm⟩

section Sizes

variable {c q r t : ℕ} {m d : Fin c → ℕ} {B : Fin c → Multiset ℂˣ}

end Sizes

def HasParts (V : HSp D) (μ : D.what₂.Tau → Fin V.rank → ℝ) (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (c : GlobalTheory.DownLift.Sys D) : Prop :=
  haveI := host_isCMField D.host
  ∃ (r : ℕ) (m d : Fin r → ℕ) (π : ∀ i, CuspSub D.host.E (m i)),
    (∀ i, 1 ≤ m i ∧ 1 ≤ d i ∧ (π i).IsCsd) ∧ ∑ i, m i * d i = V.rank ∧
    (∀ τ, ∃ A A' : Fin r → Multiset ℂ,
      (∀ i, (π i).HasInfChar (tauE D τ) (A i) ∧ (π i).HasInfChar (ComplexEmbedding.conjugate (tauE D τ)) (A' i)) ∧
      ∑ i, spehInf (d i) (A i) = Finset.univ.val.map (fun a => (μ τ a : ℂ)) ∧
      ∑ i, spehInf (d i) (A' i) = Finset.univ.val.map (fun a => -(μ τ a : ℂ))) ∧
    ∀ P, OffS D S P → ∃ B : Fin r → Multiset ℂˣ, (∀ i, GlobalTheory.LFun.HasSatGL P ((π i).locRep P) (B i)) ∧
      IsPar P V.rank (IsLab V P) (c P) (∑ i, spehSat (Formalism.ConjugateSelfDual.normV P) (d i) (B i))

section Real

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

open GlobalTheory.DownLift GlobalTheory.DownLift.Params GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars

def parV (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) (a : Fin (Vc D i).rank) : ℝ :=
  (((Bridge.lamLdef (D := D) (Vc D i).rank ((i : ℕ) + 1) τ).w a : ℤ) : ℝ) + ((rhoVec (Vc D i).rank a : ℚ) : ℝ)

end Real

end GlobalTheory.PtString

end
