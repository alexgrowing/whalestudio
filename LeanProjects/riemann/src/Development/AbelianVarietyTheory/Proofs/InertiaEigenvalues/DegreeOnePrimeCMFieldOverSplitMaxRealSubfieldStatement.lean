import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DegreeOnePrimeCMFieldOverSplitMaxRealSubfield
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotCrysAtOfMono0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIdeleCharLocalFactorization

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degreeOne_prime_CMField_over_split_maxRealSubfield : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)),
    w.asIdeal.inertiaDeg ℤ = 1 → w.asIdeal.ramificationIdx ℤ = 1 →
    Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 (maximalRealSubfield E))) ∧
    (Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) (w.under (𝓞 (maximalRealSubfield E)))).card = 2 ∧
    ∀ w' ∈ Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) (w.under (𝓞 (maximalRealSubfield E))),
      Ideal.absNorm w'.asIdeal = Ideal.absNorm w.asIdeal ∧ w'.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1 := by
  first | exact @GlobalTheory.SplitDegOne.main | exact GlobalTheory.SplitDegOne.main | (intros; apply GlobalTheory.SplitDegOne.main <;> assumption)
