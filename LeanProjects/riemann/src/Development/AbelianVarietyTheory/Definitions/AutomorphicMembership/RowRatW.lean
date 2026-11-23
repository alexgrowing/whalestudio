import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultW
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsClosedEmbeddingOfLocallyCompact
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartW

noncomputable section

namespace GlobalTheory.Mem.LiteralAutomorphy

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

structure PrM : Prop where
  m1 : GlobalTheory.Published.HarishChandraAnalyticity
  m2 : GlobalTheory.Published.DiscreteSeriesClassification
  m3 : GlobalTheory.Published.CuspRapidDecay
  m4 : GlobalTheory.Published.HarishChandraFinite
  m5 : GlobalTheory.Published.CuspTraceClass
  m6 : GlobalTheory.Published.DixmierMalliavinFactorisation
  m7 : GlobalTheory.Published.FlathFactorisation
  m8 : GlobalTheory.Published.PseudoCoefficientUpq
  m9 : GlobalTheory.Published.HarishChandraCharacters
  m10 : GlobalTheory.Published.LanglandsClassification
  m11 : GlobalTheory.Published.LabesseWaldspurger
  m12 : GlobalTheory.Published.ZelevinskyPolynomialRing
  m13 : GlobalTheory.Published.GeometricLemma
  m14 : GlobalTheory.Published.GreenCuspidal

def Mult0 : Prop := Ev fun K => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok)
  (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt), K.Over B.toPre → GrpTrue Z.N f →
    (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.Ok3 1 → z.R.toRealDat.ExAt → GlobalTheory.CuspMult.MultEq z.R.toRealDat

def MultL : Prop := StepW Pinned fun _ B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
  (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → z.R.toRealDat.ExAt → GlobalTheory.RealGeo.InGeo z.geo →
    GlobalTheory.CuspMult.MultEq z.R.toRealDat

def RowRatW : Prop := StepW Start fun K B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
  (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → DV.KapDef (w.D Z) → z.R.toRealDat.ExAt →
    GlobalTheory.RealGeo.InGeo z.geo → CoreP z → GIs2 K w Z.G → Wt = z.W1 (F0K K.s (w.D Z)) → (∀ v ∈ Wt, B.places.resChar v ∈ T.pl) →
    Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F)

theorem hypH_of (c : GlobalTheory.Published.DiscreteSeriesCover) (h1 : GlobalTheory.PrimIn.Hypotheses3) (h2 : GlobalTheory.Published.RegularisedSiegelWeilFirstTerm)
    (h3 : GlobalTheory.Published.HeckeLPartialContinuation) (m : MultL) (r : RowRatW) : HypH :=
  ⟨c, h1, h2, h3, m,
    (StepW.and ((StepW.of_all fun _ _ _ _ _ _ _ s => s.1 : StepW Start Pinned).trans m) r).trans
      (StepW.of_all fun _ _ _ _ _ _ _ G Z hX Wt z a b k c d e g u v => ⟨G.1 Z hX Wt z a b c d, G.2 Z hX Wt z a b k c d e g u v⟩)⟩

end GlobalTheory.Mem.LiteralAutomorphy

end
