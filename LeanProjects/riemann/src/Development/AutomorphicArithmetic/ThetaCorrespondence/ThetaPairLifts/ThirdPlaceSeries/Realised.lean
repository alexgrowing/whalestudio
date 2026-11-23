import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealPins
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealRec
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealRecPins
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEqAlt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
namespace GlobalTheory.BigTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC}
variable {ex : Extra D L hT Gi Gl Kc Y cX}
namespace PtAt
variable {Csz : ℝ}
set_option maxHeartbeats 1000000 in
def ofReal_alt (P : IndefiniteRowSideFullHecke ex) (Del h0 : ℕ) (hDel : D.s.Del = (Del : ℚ)) (hh0 : L.etaSz = (D.R.m : ℝ) * (h0 : ℝ))
    (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs))
    (gamDvd : (∀ (t : P.T) (c : (P.A3.A.fam.R t).S.Cl), Fintype.card ((P.A3.A.fam.R t).S.Gam c) ∣ (D.mem D.u₀).C.DGam) ∧
      ∀ (j : Fin D.R.m) (t : P.T) (c : (P.A3.A.fam.L j t).S.Cl), Fintype.card ((P.A3.A.fam.L j t).S.Gam c) ∣ (D.mem D.u₀).C.DGam)
    {Rc : _root_.Formalism.L2.RecTAlt ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} (B : _root_.Formalism.IndefR.RealTBAlt Rc P.toRowSideFamily Dcf Spf (P.zsc Del h0 Csz) S)
    (Qp : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q) (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q) : PtAt ex Csz :=
  { P := P, Del := Del, h0 := h0, hDel := hDel, hh0 := hh0, Dcf := Dcf, Spf := Spf, gamDvd := gamDvd
    T := B.T, alg := B.alg, R := B.Q.Rl
    charW := B.Q.charW, zs := B.Q.zs, s0 := B.Q.s0, s1 := B.Q.s1, dc := B.Q.dc, stdChar := B.Q.stdChar, signs := B.Q.signs
    cG := B.Q.cG, Sx := B.Q.Sx, nexp := B.Q.nexp, stdV := B.Q.stdV, stdX := B.Q.stdX, host := B.Q.host, err_eq := B.Q.err_eq
    vpos := B.Q.vpos
    κ := B.κ, v₀ := B.v₀, fw := B.fw, bar := B.bar, O := B.O, pins := B.pins, rhoGeo := B.rhoGeo, equivAll := B.equivAll
    cTie := B.cTie, phase := B.phase
    qGuard := Qp.qGuard, hF := Qp.hF, phsOne := Qp.phsOne, prXunit := Qp.prXunit, grpRecPin := Qp.grpRecPin, fdiag := Qp.fdiag
    eGtie := Qp.eGtie, betaStd := Qp.betaStd
    tupT := Qr.tupT, hm := Qr.hm, Tp := Qr.Tp, tupXi := Qr.recR.tupXi, tupAt := Qr.recR.tupAt, tupTie := Qr.tupTie
    tupT_tup := Qr.tupT_tup, muEq := Qr.muEq }
variable (p : PtAt ex Csz)
def RealisedCondition : Prop :=
  ∃ (Rc : _root_.Formalism.L2.RecTAlt ex) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc)
    (B : _root_.Formalism.IndefR.RealTBAlt Rc p.P.toRowSideFamily p.Dcf p.Spf (p.P.zsc p.Del p.h0 Csz) S) (Qp : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q) (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q),
    _root_.Formalism.IndefR.IndefiniteRealisationCompatible Qp Qr ∧ _root_.GlobalTheory.BigTop.PtAt.ofReal_alt p.P p.Del p.h0 p.hDel p.hh0 p.Dcf p.Spf p.gamDvd B Qp Qr = p
structure CompatibilityConditions : Prop where
  real : p.RealisedCondition
  core : GlobalTheory.BigOn.CoreTies L ex.errX p.T p.R.toRealDat
  pb : p.T.pb = p.R.C.P.pb
  types : GlobalTheory.DimPartsCompare.TameTie D p.R.C.W.om
  series : Nonempty (GlobalTheory.SeriesTie.ExportTie p.nexp p.v₀)
  level : p.LevelTie
  data : p.DataTie
  psiVal : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (p.Tp.psi w).ValuesIn 0 D.what₂.embLL
  ray : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (Formalism.L2.Host.embLL0 D).fieldRange
  roots : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (Formalism.L2.Host.embLL0 D).fieldRange
  rayQ : ∀ t, GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.embK D) (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.tupLevel p.R.toRealDat t)
  twist : GlobalTheory.EX.DQ.TwAllAt D ex.nch ex.xd
structure PointConditions' : Prop where
  exAt : p.R.toRealDat.ExAt
  jEvBar : JEvBar p.T p.R.toRealDat p.κ
  geoAct : GeoAct p.T p.R.toRealDat p.κ p.v₀
  evInj : EvInj p.T p.R.toRealDat p.v₀
  ioExt : IoExt p.R.toRealDat
  oneMap : ∀ i, OneMapRowR p.T p.R.toRealDat p.κ p.v₀ p.O (phEff p.R) i
  prim : PrimRows3 p.R p.F
  sep : p.P.A3.fam3.TypesSep3
  ok : p.P.A3.fam3.Ok3 1
  framesOK : Formalism.IndefR.Mi.FramesOKg2 p.R
  divRows : DivRows3 D p.P.A3 p.P.P0 p.P.ψ0 p.P.Ps p.P.ψs p.P.Zs p.P.S0 p.P.S1 ex.p0 p.P.C p.P.NuC p.P.I
  psi : PsiPPTie D p.P.P0 p.P.ψ0 p.P.Ps p.P.ψs p.P.I.eG
  d0 : D.what₂.D0 = (p.P.A3.A.fam.R p.P.A3.A.fam.μ0).dZ (p.P.A3.A.fam.lvl p.P.P0 p.P.ψ0) (p.P.Zs.Z p.P.A3.A.fam.μ0)
  export_ : p.ExportRow
  goodFT : Formalism.BasicNotions.GoodFTAll D
  w1 : ∀ w, (p.R.toCx3 p.F).W1 p.F.cr (p.N 0 0) w → w ∈ p.R.twPl
  ties : p.CompatibilityConditions
section OfReal
variable {P : IndefiniteRowSideFullHecke ex} {Del h0 : ℕ} {hDel : D.s.Del = (Del : ℚ)} {hh0 : L.etaSz = (D.R.m : ℝ) * (h0 : ℝ)}
  {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)}
  {gamDvd : (∀ (t : P.T) (c : (P.A3.A.fam.R t).S.Cl), Fintype.card ((P.A3.A.fam.R t).S.Gam c) ∣ (D.mem D.u₀).C.DGam) ∧
    ∀ (j : Fin D.R.m) (t : P.T) (c : (P.A3.A.fam.L j t).S.Cl), Fintype.card ((P.A3.A.fam.L j t).S.Gam c) ∣ (D.mem D.u₀).C.DGam}
  {Rc : _root_.Formalism.L2.RecTAlt ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {B : _root_.Formalism.IndefR.RealTBAlt Rc P.toRowSideFamily Dcf Spf (P.zsc Del h0 Csz) S}
  {Qp : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q} {Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q}
end OfReal
namespace Realised
variable {p} (h : p.RealisedCondition)
include h
theorem _root_.GlobalTheory.BigTop.PtAt.RealisedCondition.induction {Q : PtAt ex Csz → Prop}
    (hQ : ∀ (Rc : _root_.Formalism.L2.RecTAlt ex) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc)
      (B : _root_.Formalism.IndefR.RealTBAlt Rc p.P.toRowSideFamily p.Dcf p.Spf (p.P.zsc p.Del p.h0 Csz) S) (Qp : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q) (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q),
      _root_.Formalism.IndefR.IndefiniteRealisationCompatible Qp Qr → Q (_root_.GlobalTheory.BigTop.PtAt.ofReal_alt p.P p.Del p.h0 p.hDel p.hh0 p.Dcf p.Spf p.gamDvd B Qp Qr)) : Q p :=
  let ⟨Rc, S, B, Qp, Qr, a, e⟩ := h
  Eq.subst (motive := Q) e (hQ Rc S B Qp Qr a)
theorem _root_.GlobalTheory.BigTop.PtAt.RealisedCondition.tiedRec : _root_.Formalism.L2.ExtraDataRecursive ex := let ⟨Rc, _⟩ := h; ⟨Rc⟩
theorem _root_.GlobalTheory.BigTop.PtAt.RealisedCondition.exists_frame : ∃ Rc : _root_.Formalism.L2.RecTAlt ex, p.R.C = Rc.T.n.cf ∧ HEq p.Tp Rc.T.n.tp ∧ p.R.ψ = Rc.T.theta.W.ψ :=
  h.induction (Q := fun p => ∃ Rc : _root_.Formalism.L2.RecTAlt ex, p.R.C = Rc.T.n.cf ∧ HEq p.Tp Rc.T.n.tp ∧ p.R.ψ = Rc.T.theta.W.ψ)
    fun Rc _ B Qp Qr _ => ⟨Rc, Qp.cfEq, Qr.tpEq, B.Q.psiPin⟩
theorem _root_.GlobalTheory.BigTop.PtAt.RealisedCondition.valLL0 : Formalism.L2.Host.ValLL0 D p.R.C := by
  obtain ⟨Rc, e, -⟩ := h.exists_frame
  exact e ▸ Rc.T.chrVal
theorem _root_.GlobalTheory.BigTop.PtAt.RealisedCondition.psiChoice : Formalism.L2.Host.PsiChoiceCompatible D p.R.C ex.nch p.Tp := by
  obtain ⟨Rc, e, e', -⟩ := h.exists_frame
  have := Rc.T.chrPsi
  revert e'
  generalize p.Tp = t
  generalize p.R.C = c at e t ⊢
  subst e
  intro e'
  exact eq_of_heq e' ▸ this
end Realised
theorem CompatibilityConditions.eSer {p : PtAt ex Csz} (h : p.CompatibilityConditions) : GlobalTheory.GLq.ESerTie D := h.types.eSerTie
end PtAt
def EventuallyAtPoints {eps : ℝ} (Fm : FamP eps) (Q : ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop) : Prop :=
  ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ (i : Fm.Ix x) (p : Pt Fm x hx i), p.PointConditions' → Q x hx i p
theorem EventuallyAtPoints.of_forall {eps : ℝ} {Fm : FamP eps} {Q : ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop}
    (h : ∀ x hx i p, p.PointConditions' → Q x hx i p) : _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm Q := ⟨0, fun x hx _ => h x hx⟩
theorem EventuallyAtPoints.and {eps : ℝ} {Fm : FamP eps} {Q Q' : ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop}
    (h : _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm Q) (h' : _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm Q') : _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x hx i p => Q x hx i p ∧ Q' x hx i p :=
  let ⟨a, h⟩ := h
  let ⟨b, h'⟩ := h'
  ⟨max a b, fun x hx hle i p hp => ⟨h x hx ((le_max_left _ _).trans hle) i p hp, h' x hx ((le_max_right _ _).trans hle) i p hp⟩⟩
def LambdaLowerBound₂ : Prop := Closed FamHyp fun Fm CH => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun _ _ _ p => ∀ C, (p.S true).L6 (p.N C CH)
end GlobalTheory.BigTop
end
end
