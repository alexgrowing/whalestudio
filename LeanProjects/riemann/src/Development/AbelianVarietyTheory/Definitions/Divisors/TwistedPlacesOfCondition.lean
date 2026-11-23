import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartW
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodGeneric
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LowerLiftsZeroOfWittIdxEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SiegelWeilAnisotropicUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SchurOrthogonalitySquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TupPrimeEmpty
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Formalism.LocalToGlobal.IndefiniteReal.RealTB
import Formalism.LocalToGlobal.IndefiniteReal.RealPins

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PrimIn

structure Hypotheses₂ : Prop where
  p1 : GlobalTheory.Hk3.HoweUnram
  p2 : GlobalTheory.Published.CuspRapidDecay
  p3 : GlobalTheory.Published.HarishChandraFinite
  p4 : GlobalTheory.Published.WeilRepresentationUnitaryPair
  p5 : GlobalTheory.Published.GreenCuspidal
  p6 : GlobalTheory.Published.BernsteinUnitaryProductIrreducible
  p7 : GlobalTheory.Published.BernsteinZelevinskyFiniteness
  p8 : GlobalTheory.Published.FlathFactorisation
  p9 : GlobalTheory.Published.CuspTraceClass
  p10 : GlobalTheory.Published.RallisInnerProductConvergent
  p11 : GlobalTheory.Published.SiegelWeilAnisotropicUnitary
  p12 : GlobalTheory.Published.HeckeLPartialContinuation
  p13 : GlobalTheory.Published.HermitianLocalGlobal
  p14 : GlobalTheory.Published.DoublingMethod
  p15 : GlobalTheory.Published.SchurOrthogonalitySquareIntegrable
  p16 : GlobalTheory.Published.UnramifiedDoublingGL
  p17 : GlobalTheory.Published.WeilSiegelFormulaUnitary
  p18 : GlobalTheory.Published.ZelevinskyPolynomialRing
  p19 : GlobalTheory.Published.DiscreteSeriesCover
  p20 : GlobalTheory.Published.CuspidalMirabolic
  p21 : GlobalTheory.Published.HarishChandraModules
  p22 : GlobalTheory.Published.SiegelWeilUnitaryConvergent
  p23 : GlobalTheory.Published.GeometricLemma
  p24 : GlobalTheory.Published.CasselmanWallach
  p25 : GlobalTheory.Published.RegularisedSiegelWeilFirstTerm
  p26 : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent

theorem Hypotheses₂.eisenstein (h : Hypotheses₂) : GlobalTheory.Published.SiegelEisensteinContinuation :=
  GlobalTheory.Published.siegelEisensteinContinuation_of_doublingMethod h.p14

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}

def SerClause (D : D7) : Prop :=
  ∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∃ (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod (D.host.g k))) (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k)) C),
      ∀ f, D.ntypes.eSer k f = Formalism.L2.NT.eSerO O D.R.r f

structure TiesA {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) : Prop where
  ok : A3.fam3.Ok3 1
  char : R.WeakCharacterisation F
  ex : R.toRealDat.ExAt
  host : Formalism.IndefR.Links.HostHyp D
  params : ∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)
  ccK : D.host.ccK = ⊤
  guard : QGuard R.toRealDat
  types : GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R.toRealDat
  ser : SerClause D
  junk : GlobalTheory.Hk3.InertJunk A3
  trSem : (∃ tr, R.TrISem F tr ∧ GlobalTheory.Hk3.TrISepWith A3 tr) → R.TrISem F A3.trI ∧ A3.fam3.TrISep
  std : IsStdChar D R.ψ (-1)
  phs : ∀ i, R.phs i = 1
  w1 : ∀ w, (R.toCx3 F).W1 F.cr (R.num F 0 0) w → w ∈ R.twPl
  nV : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV

structure TiesG (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec)
    (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) : Prop where
  fw : ∃ fw : FWTie T R.toRealDat κ v₀, BarTie fw
  pins : ∀ i, OMPins T R.toRealDat κ v₀ O i
  phase : ∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => cj (twAt D.what₂.embLL A3.A.v0) (R.phs i)) i
  unif : R.toRealDat.LUnif
  ioExt : IoExt R.toRealDat
  oneMap : ∀ i, OneMapRowR T R.toRealDat κ v₀ O (fun i => cj (twAt D.what₂.embLL A3.A.v0) (R.phs i)) i
  cover : GlobalTheory.TwistField.CoverField T R.toRealDat

structure Inputs {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) : Prop where
  mult : GlobalTheory.CuspMult.MultEq R.toRealDat
  rallis : GlobalTheory.RawLift.RallisConv D
  nonVan : ∀ i t, GlobalTheory.DownLift.NonVan R.toRealDat i t
  rowTest : Formalism.IndefR.Rat.RowTest (R.toCx3 F)

section Real

open Formalism.L2 Formalism.L2.Rows

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
  {Rc : Formalism.L2.RecT ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc}

theorem serClause_of_rec (Rc : Formalism.L2.RecT ex) : SerClause D :=
  fun k => ⟨_, Rc.T.n.types.O k, Rc.T.n.types.eSer_def k⟩

theorem TiesA.of_real {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Q : RealT Rc P Dcf Spf Zscf S Ks)
    (hP : RealPins Q) (ok : P.A3.fam3.Ok3 1) (hex : Q.Rl.toRealDat.ExAt) (par : Nonempty (ParameterChoice' D L))
    (cc : D.host.ccK = ⊤) (ty : GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes Q.Rl.toRealDat) (junk : GlobalTheory.Hk3.InertJunk P.A3)
    (w1 : ∀ w, (Q.Rl.toCx3 Q.F).W1 Q.F.cr (Q.Rl.num Q.F 0 0) w → w ∈ Q.Rl.twPl)
    (nV : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) : TiesA Q.Rl Q.F :=
  ⟨ok, Q.charW, hex, Q.host, ⟨L, par⟩, cc, hP.qGuard, ty, serClause_of_rec Rc, junk, Q.trSem, Q.stdChar, hP.phsOne, w1, nV⟩

theorem TiesG.of_real (B : RealTB Rc P Dcf Spf Zscf S) (hB : RowsB B) (hU : B.Q.Rl.toRealDat.LUnif)
    (hC : GlobalTheory.TwistField.CoverField B.T B.Q.Rl.toRealDat) : TiesG B.T B.Q.Rl B.κ B.v₀ B.O :=
  ⟨⟨B.fw, B.bar⟩, B.pins, B.phase, hU, hB.ioExt, hB.oneMap, hC⟩

end Real

section Api

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3}

theorem TiesA.twistedPlaces_of_condition (h : TiesA R F) (C CH : ℝ) : ∀ w, (R.toCx3 F).W1 F.cr (R.num F C CH) w → w ∈ R.twPl := h.w1

theorem TiesA.char3 (h : TiesA R F) : R.Char3 F := RealDat3.characterisation_of_weak h.char h.ex

example (h : TiesA R F) : 4 ≤ D.R.nV := le_trans (Nat.le_add_left _ _) h.nV

example (i : Fin D.R.m) (hi : R.phs i ≠ 1) : ¬ TiesA R F := fun h => hi (h.phs i)

theorem TiesG.phaseTie {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat3 D A3 T.Q.c.F}
    {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec}
    {O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)} (h : TiesG T R κ v₀ O) (i : Fin D.R.m) :
    PhaseTie T R.toRealDat κ v₀ O (fun i => cj (twAt D.what₂.embLL A3.A.v0) (R.phs i)) i :=
  h.phase i h.unif

end Api

end GlobalTheory.PrimIn

end
