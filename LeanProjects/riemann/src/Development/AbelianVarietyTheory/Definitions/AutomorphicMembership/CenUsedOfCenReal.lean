import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OExt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsIdealsPrimeToEqSpan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsValueTiedOfIsToricElt
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight

noncomputable section

namespace GlobalTheory.HeightCounting.Up

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure PrN : Prop where
  what₂ : GlobalTheory.NRows.Hypotheses₂
  decay : GlobalTheory.Published.CuspRapidDecay
  hc : GlobalTheory.Published.HarishChandraFinite
  greenC : GlobalTheory.Published.GreenCuspidal
  green : GlobalTheory.GLq.Green
  zel : GlobalTheory.Published.ZelevinskyPolynomialRing
  dz : GlobalTheory.Published.DepthZeroInertia
  ray : GlobalTheory.Published.RayClassFieldSt
  rayF : GlobalTheory.NT.RayField
  rayA : GlobalTheory.Published.RayCharacterArtin
  bc : GlobalTheory.Published.BaseChangeDefiniteUnitary
  ds : GlobalTheory.Published.DiscreteSpectrumGL
  gen : GlobalTheory.Published.GenericUnitaryDualGL
  std : GlobalTheory.Published.StandardCosocleGL
  cheb : GlobalTheory.TwSys.Cheb
  howe : GlobalTheory.Hk3.HoweUnram

structure SerN : Prop where
  rat : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat
  int : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt
  hkInt : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt
  hkTr : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform
  hkRead : GlobalTheory.HeckeSupSt.HeckeReadTie
  ratio : GlobalTheory.ToricRational.RatioConj

abbrev LayP (hL : GlobalTheory.Published.LocalLanglandsGL) : Type 1 :=
  ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl)
    (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch), NCore hL t n → Prop

def AtMem (hL : GlobalTheory.Published.LocalLanglandsGL) (p : LayP hL) : Prop :=
  EvLgG fun K B f T => KPx B f → ∀ w Z Wt p0 t nch n xd c, Nonempty (NE hL K B f T w Z Wt p0 t nch n xd c) → Nonempty (RXs t) →
    ColPin w → p K B f T w Z Wt p0 t nch n c

def CenUsed (D : D7) (M : MtFam D) : Prop :=
  ∀ (μ : D.what₂.Tup), Formalism.IndefR.RecTie.Used0 D μ → ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), ∃ L : G0g D.nd → GAf D.host.E D.R.nV,
    GlobalTheory.PendOf.IsTypeGroupBlockLift D D.R.nV L ∧ ∀ (z : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) (x : D.what₂.Mt μ j),
      (M μ j h1 h2).real (D.ntypes.cenMt μ j z x) =
        GlobalTheory.PendOf.actSum D L (z : MonoidAlgebra ℂ (G0g D.nd)) ((M μ j h1 h2).real x)

theorem cenUsed_of_cenReal {D : D7} {M : MtFam D} (h : GlobalTheory.PendOf.CenReal D M) : CenUsed D M := fun μ _ => h μ

def SumUsed (D : D7) (M : MtFam D) : Prop :=
  ∀ (μ : D.what₂.Tup), Formalism.IndefR.RecTie.Used0 D μ → ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), GlobalTheory.CoefDuty.ClassSum (M μ j h1 h2)

def RootsLL (D : D7) : Prop := ∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ D.what₂.restRowsFiniteGroupCard

structure PinAt {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (a : NAt hL D cf nch tp) (P : GlobalTheory.NPin.Pin hL D) : Prop where
  cf_eq : P.cf = cf
  C_eq : P.C = nch
  tp_eq : HEq P.tp tp
  rep_eq : HEq P.rep a.nt.rep
  M_eq : P.M = a.all.gal.mt
  lab : GlobalTheory.PendOf.LabAll D P.T
  green : GlobalTheory.PendOf.GreenLab P.ty.grp
  chiT : ChiTOk D P.cf

def ParSt (hL : GlobalTheory.Published.LocalLanglandsGL) : Prop :=
  AllSt fun _ _ _ _ _ _ x => ∀ l : LA hL x, GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam (Dof x) l.a.A.row

def SXd (hL : GlobalTheory.Published.LocalLanglandsGL) : Prop :=
  AllSt fun _ _ _ _ _ _ x => SeriesLevel hL x → ∃ xd : ThData (Dof x), XdAll xd

def PtSt (hL : GlobalTheory.Published.LocalLanglandsGL) : Prop :=
  AllSt fun _ _ _ _ _ _ x => ∀ l : LC hL x, GlobalTheory.CoefDuty.EvO l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' =>
    (SumRepresentations.hypO D' → SumRepresentations.Conclusion41 D' ∧ AutomorphicSideWildInertia.ResidualIrreducibleGood D' ∧ SumRepresentations.Conclusion42 D' ∧ SumRepresentations.ConclusionZ D') ∧ D'.nd.EigSpan ∧ Rows.IsotInternal D'.what₂

end GlobalTheory.HeightCounting.Up

end
