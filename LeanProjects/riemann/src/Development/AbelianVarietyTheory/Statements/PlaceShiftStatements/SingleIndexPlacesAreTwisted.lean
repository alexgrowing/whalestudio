import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceLatticeLeThetaLatticeAtPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeafTW1OfAllConjugatesGood
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoverFieldOfContainsRayField
import Formalism.LocalToGlobal.UnitaryNorms.CharGal

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

namespace GlobalTheory.BigOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Record

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

def LevelIs {G : Type} [Group G] (e : G ≃* G0g N) (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) : Prop :=
  (∀ g, e g ∈ Y.U ↔ g ∈ U) ∧ ∀ (i : X.Tw) (b : Bool) (u : U) (h : e u ∈ Y.U), ∃ x : D.LL0,
    (x : D.what₂.LL) = (ψ u : D.what₂.LLˣ) ∧
      ((Y.psiU i b ⟨e u, h⟩ : (FractionRing (X.O i))ˣ) : FractionRing (X.O i)) = GlobalTheory.SeriesTie.sideEmb X i b x

def AllData (S : ∀ i j b, Set (Y.Dat i j b)) : Prop :=
  ∀ (i : X.Tw) (j : Fin D.R.m) (b : Bool) (a : Y.Dat i ((j : ℕ) + 1) b),
    (∀ u : Y.U, Y.actG i _ b u (Y.th i _ b a) =
      ((Y.psiU i b u : (FractionRing (X.O i))ˣ) : FractionRing (X.O i)) • Y.th i _ b a) → a ∈ S i _ b

structure SmallHas (D : D7) (C : Formalism.L2.Host.CharFrame D) : Prop where
  val : Formalism.L2.Host.ValLL0 D C
  ray : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (Formalism.L2.Host.embLL0 D).fieldRange
  roots : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (Formalism.L2.Host.embLL0 D).fieldRange

end Record

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

def F2 : Face D p.P.A3.A :=
  { p.F.lv2 with
    Zsc := fun _ => ⟨p.Z.F0, p.Z.J0, p.Z.E1u, p.Z.l3m, p.Z.l3u, p.Z.l6m, p.Z.l6u, p.Z.x, p.Z.b, p.Z.la, p.Z.de⟩ }

def R2 : RealDat D p.P.A3.A p.T.Q.c.F := charOf p.R.toRealDat (F2 p)

def fw2 : FWTie p.T (R2 p) p.κ p.v₀ := reFw p.fw (F2 p)

def om2 (i : Fin D.R.m) : OMDat p.T.toCore (R2 p) i Unit (fun _ => p.P.A3.A.μ0) := reOM (p.O i) (F2 p)

abbrev S2 := ((R2 p).toCx (F2 p)).data (F2 p).cr false

def SingleIndexPlacesAreTwisted : Prop := ∀ w, (p.R.toCx3 p.F).W1 p.F.cr (p.N 0 0) w → w ∈ p.R.twPl

structure RecTies : Prop where

  series : Nonempty (GlobalTheory.SeriesTie.ExportTie p.nexp p.v₀)

  level : LevelIs D.nexp (p.R.eG.trans p.cG) p.P.P0 p.P.ψ0⁻¹

  data : AllData D.nexp ex.xd.xd0

  psi : Formalism.L2.Host.PsiChoiceCompatible D p.R.C ex.nch p.Tp

  psiVal : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (p.Tp.psi w).ValuesIn 0 D.what₂.embLL

  small : SmallHas D p.R.C

  types : GlobalTheory.DimPartsCompare.TameTie D p.R.C.W.om

  rayQ : ∀ t, GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.embK D) (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.tupLevel (R2 p) t)

def More : Prop := SingleIndexPlacesAreTwisted p ∧ CoreTies L ex.errX p.T (R2 p) ∧ RecTies p

def Links2 : Prop :=
  (R2 p).Char (F2 p) ∧ p.P.A3.A.fam.Ok 1 ∧ (R2 p).LUnif ∧ BaseLinks (R2 p) (F2 p) ∧ RankRows (S2 p) ∧ BarTie (fw2 p) ∧
    (∀ i, OMPins p.T (R2 p) p.κ p.v₀ (om2 p) i) ∧ ∀ i, PhaseTie p.T (R2 p) p.κ p.v₀ (om2 p) (fun _ => 1) i

abbrev Obj (c : OnConst) : Type := OnObj (S2 p) (Mir (R2 p)) c

def RecAt {Pm : ParameterChoice' D L} (Tp : ParamsT D L Pm) (r : TwoRuns p.T p.P.Gp) {c : OnConst} (O : Obj p c) : Prop :=
  IsRec Tp ex.kap_def ex.errX (F2 p) (fw2 p) r O ∧ OwnPin r

end Point

def AtPts (Q : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop) : Prop :=
  Closed FamHyp fun Fm _ => EvPt Fm fun x hx i p => More p → Q Fm x hx i p

def AtRuns (Q : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i) (r : TwoRuns p.T p.P.Gp),
    RunsOk (fw2 p) r → Prop) : Prop :=
  AtPts fun Fm x hx i p => ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → Q Fm x hx i p r h

def AtRec (Q : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i) (c : OnConst),
    Obj p c → Prop) : Prop :=
  Closed FamHyp fun Fm _ => ∃ c0 : ℝ, ∀ c : OnConst, c0 ≤ c.C → OnPage.ConstBad c →
    EvPt Fm fun x hx i p => More p → ∀ (r : TwoRuns p.T p.P.Gp) (O : Obj p c), RecAt p (Fm.parT x hx i) r O → Q Fm x hx i p c O

def RunsSt : Prop := AtPts fun _ _ _ _ p => ∃ r : TwoRuns p.T p.P.Gp, RunsOk (fw2 p) r ∧ OwnPin r

def RatSt : Prop := AtPts fun _ _ _ _ p => TwistedRational (R2 p) (F2 p) fun _ => 1

def ExportSt : Prop := AtPts fun Fm x hx i p => ∀ v ∈ p.R.twPl, ∀ j,
  GlobalTheory.TwistIndex.ExportTie p.P.A3.A (Fm.ex x hx i).nch (twE Fm x hx i) (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹ 1 v (ownAt (Fm.D x i) v)

def MaxSt : Prop := AtPts fun Fm x _ i p => ∀ v ∈ p.R.twPl, ∀ j,
  GlobalTheory.TraceClassRank.SpanOverClasses (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹ 1 v (ownAt (Fm.D x i) v)

def FullSt : Prop := AtPts fun Fm x _ i p => ∀ v ∈ p.R.twPl, ∀ j,
  GlobalTheory.TraceClassRank.ClassFullRank (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹ 1 v (ownAt (Fm.D x i) v)

def CmpSt : Prop := AtRuns fun Fm x _ i p r h => ∀ v ∈ p.R.twPl, ∀ j,
  letI : Algebra (r.used v).full.J.Q.c.F (Fm.D x i).what₂.LL := p.alg
  GlobalTheory.TraceClassRank.CompareOffOwn (T := (r.used v).full) (R := R2 p) (h.laws v).p (fw2 p) j (r.lev j) (F2 p).P0 (F2 p).ψ0⁻¹ 1 v
               (ownAt (Fm.D x i) v) ∧
    GlobalTheory.TraceClassRank.CompareSpan (T := (r.used v).full) (R := R2 p) (h.laws v).p (fw2 p) j (r.lev j) (F2 p).P0 (F2 p).ψ0⁻¹ 1 v
      (ownAt (Fm.D x i) v)

def OwnSt : Prop := AtRuns fun Fm x _ i p r h => ∀ v ∈ p.R.twPl, ∀ j,
  letI : Algebra (r.used v).full.J.Q.c.F (Fm.D x i).what₂.LL := p.alg
  GlobalTheory.TraceClassRank.CompareAtOwn (T := (r.used v).full) (R := R2 p) (h.laws v).p (fw2 p) j (r.lev j) (F2 p).P0 (F2 p).ψ0⁻¹ 1 v
    (ownAt (Fm.D x i) v)

def GeoSt : Prop := AtRec fun _ _ _ _ p _ O => LeafSup O ∧ LeafSpan O ∧ LeafLemmaS O ∧ LeafData O ∧ HasIndexBound O ∧
  ∀ C CH, LeafDepthGood ((R2 p).num (F2 p) C CH) O ∧ LeafDepthRam ((R2 p).num (F2 p) C CH) O ∧
    LeafDepth2 ((R2 p).num (F2 p) C CH) O ∧ LeafDepthLevel ((R2 p).num (F2 p) C CH) O

def RankSt : Prop := AtRec fun _ _ _ _ _ _ O => LeafRankJ O

def RankLocSt : Prop := AtRec fun _ _ _ _ _ _ O => GlobalTheory.TraceClassRank.RankAtPlaces O

def CmpOffSt : Prop := AtRuns fun Fm x _ i p r h => ∀ v ∈ p.R.twPl, ∀ j,
  letI : Algebra (r.used v).full.J.Q.c.F (Fm.D x i).what₂.LL := p.alg
  GlobalTheory.TraceClassRank.CompareOffOwn (T := (r.used v).full) (R := R2 p) (h.laws v).p (fw2 p) j (r.lev j) (F2 p).P0 (F2 p).ψ0⁻¹ 1 v
    (ownAt (Fm.D x i) v)

def ExportSt0 : Prop := Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ (i : Fm.Ix x) (p : Pt Fm x hx i),
  p.R.toRealDat.ExAt → JEvBar p.T p.R.toRealDat p.κ → GeoAct p.T p.R.toRealDat p.κ p.v₀ → EvInj p.T p.R.toRealDat p.v₀ →
  IoExt p.R.toRealDat → (∀ j, OneMapRowR p.T p.R.toRealDat p.κ p.v₀ p.O (phEff p.R) j) → PrimRows3 p.R p.F → p.P.A3.fam3.Ok3 1 →
  Formalism.IndefR.Mi.FramesOKg2 p.R → PsiPPTie (Fm.D x i) p.P.P0 p.P.ψ0 p.P.Ps p.P.ψs p.P.I.eG → More p → ∀ v ∈ p.R.twPl, ∀ j,
    GlobalTheory.TwistIndex.ExportTie p.P.A3.A (Fm.ex x hx i).nch (twE Fm x hx i) (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹ 1 v (ownAt (Fm.D x i) v)

theorem ExportSt0.exportSt (h : ExportSt0) : ExportSt :=
  Closed.imp h fun _ _ _ ⟨x0, H⟩ => ⟨x0, fun x hx h0 i p r => H x hx h0 i p r.exAt r.jEvBar r.geoAct r.evInj r.ioExt r.oneMap r.prim r.ok
    r.framesOK r.psi⟩

def TwistSt : Prop := AtRec fun _ _ _ _ _ _ O => HasTwistBound O

def ShareSt : Prop := AtRec fun _ _ _ _ _ _ O => LeafShareI O

def BadSt : Prop := AtRec fun _ _ _ _ _ _ O => LeafBadShare O

def ExpSt : Prop := AtRec fun _ _ _ _ p _ O => ∀ C CH, HasExpBound ((R2 p).num (F2 p) C CH) O

def PageSt : Prop := AtRec fun Fm x _ i p _ O => LeafPage O ∧ LeafSizes O ∧ LeafX O ∧ LeafBad O ∧
  LeafLevelSq O (Res (R2 p)) (Fm.D x i).R.f ∧ LeafYBound O ∧ O.b = (Fm.L x i).sc.b ∧ 0 ≤ p.Z.E1u ∧
    ∀ C CH, ErrorConstantMatchesDefinition ((R2 p).num (F2 p) C CH) O C

def OntoX : Prop := Closed FamHyp fun Fm CH => DIVinN Fm →
  ∃ C0 : ℝ, 0 ≤ C0 ∧ EvPt Fm fun _ _ _ p => More p → ∀ C, C0 ≤ C → (p.S false).ON (p.N C CH)

def AdelSt : Prop := Closed FamHyp fun Fm _ => EvPt Fm fun _ _ _ p => SingleIndexPlacesAreTwisted p →
  GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.AdelicLiftScalar (R2 p) (F2 p)

def GalSt : Prop := Closed FamHyp fun Fm _ => EvPt Fm fun _ _ _ p => SingleIndexPlacesAreTwisted p →
  GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.GalLiftFor p.T (R2 p) (F2 p) p.κ p.v₀ (om2 p) fun _ => 1

def LowNumSt : Prop := Closed FamHyp fun Fm _ => EvPt Fm fun x _ i p =>
  (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Sizes (Fm.D x i) j (Fm.L x i).sc.b) ∧ GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.PrimeToHost (R2 p) p.P.A3.A.μ0 ∧
    ∀ j, p.Z.l6m j ≤ lowB (Fm.D x i) j (Fm.L x i).sc.b

def LamLowX : Prop := Closed FamHyp fun Fm CH => EvPt Fm fun _ _ _ p => SingleIndexPlacesAreTwisted p → ∀ C, (p.S true).L6 (p.N C CH)

theorem ontoX_of_onto (h : Onto) : OntoX :=
  Closed.imp h fun _ _ _ H hD => by
    obtain ⟨C0, h0, x0, hx⟩ := H hD
    exact ⟨C0, h0, x0, fun x h1 h2 i p hp _ => hx x h1 h2 i p hp⟩

theorem OntoX.at_sel (h : OntoX) {𝒞 : FamClass} (h𝒞 : ∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → FamHyp Fm)
    (Sel : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop)
    (hS : Closed 𝒞 fun Fm _ => EvPt Fm fun x hx i p => Sel Fm x hx i p → More p) :
    Closed 𝒞 fun Fm CH => DIVinN Fm →
      ∃ C0 : ℝ, 0 ≤ C0 ∧ EvPt Fm fun x hx i p => Sel Fm x hx i p → ∀ C, C0 ≤ C → (p.S false).ON (p.N C CH) := by
  have h' : Closed 𝒞 fun Fm CH => DIVinN Fm →
      ∃ C0 : ℝ, 0 ≤ C0 ∧ EvPt Fm fun _ _ _ p => More p → ∀ C, C0 ≤ C → (p.S false).ON (p.N C CH) := by
    obtain ⟨a, ha, H⟩ := h
    refine ⟨a, ha, fun e he hle => ?_⟩
    obtain ⟨K, hK⟩ := H e he hle
    exact ⟨K, fun Fm CH hc hL => hK Fm CH (h𝒞 Fm hc) hL⟩
  refine (h'.and hS).imp fun Fm CH _ H hD => ?_
  obtain ⟨C0, h0, x0, hx⟩ := H.1 hD
  obtain ⟨x1, hx1⟩ := H.2
  exact ⟨C0, h0, max x0 x1, fun x h1 h2 i p hp hs =>
    hx x h1 ((le_max_left _ _).trans h2) i p hp (hx1 x h1 ((le_max_right _ _).trans h2) i p hp hs)⟩

theorem lamLowX_iff : LamLowX ↔ LamLow :=
  ⟨fun h => Closed.imp h fun _ _ _ ⟨x0, hx⟩ => ⟨x0, fun x h1 h2 i p hp => hx x h1 h2 i p hp hp.w1⟩,
    fun h => Closed.imp h fun _ _ _ ⟨x0, hx⟩ => ⟨x0, fun x h1 h2 i p hp _ => hx x h1 h2 i p hp⟩⟩

section Checks

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.SeriesTie
open scoped TensorProduct

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)
  {G : Type} [Group G] (e : G ≃* G0g N) (U : Subgroup G) (ψ : U →* D.what₂.LLˣ)

def smallChar (h : ∀ u, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) ∈ D.LL0) : U →* D.LL0 where
  toFun u := ⟨_, h u⟩
  map_one' := Subtype.ext (by simp)
  map_mul' u v := Subtype.ext (by simp)

def withLevel (h : ∀ u, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) ∈ D.LL0) : NExp D.R D.host D.what₂ D.LL0 N X :=
  { Y with
    U := U.comap e.symm.toMonoidHom
    psiU := fun i b => (((sideEmb X i b).toMonoidHom.comp (smallChar U ψ h)).toHomUnits).comp
      (e.symm.toMonoidHom.subgroupComap U) }

theorem levelIs_withLevel (h : ∀ u, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) ∈ D.LL0) : LevelIs (withLevel Y e U ψ h) e U ψ := by
  refine ⟨fun g => ?_, fun i b u hu => ⟨smallChar U ψ h u, rfl, ?_⟩⟩
  · change e.symm (e g) ∈ U ↔ _
    rw [e.symm_apply_apply]
  · change sideEmb X i b (smallChar U ψ h ⟨e.symm (e u), _⟩) = _
    simp only [e.symm_apply_apply]

def typedData (i : X.Tw) (j : ℕ) (b : Bool) : Set (Y.Dat i j b) :=
  {a | ∀ u : Y.U, Y.actG i j b u (Y.th i j b a) =
    ((Y.psiU i b u : (FractionRing (X.O i))ˣ) : FractionRing (X.O i)) • Y.th i j b a}

theorem exists_allData (D : D7) : (∃ T : ThData D, AllData D.nexp T.xd0) ∧ ∀ T : ThData D, AllData D.nexp T.xd0 →
    ∀ i (j : Fin D.R.m) b, T.xd0 i ((j : ℕ) + 1) b = typedData D.nexp i _ b :=
  ⟨⟨⟨typedData D.nexp, fun _ _ _ _ h => h⟩, fun _ _ _ _ h => h⟩,
    fun T h i j b => Set.ext fun a => ⟨T.thetaBase_invariant_action i _ b a, h i j b a⟩⟩

variable {Y e U ψ}

theorem joint_withAll {ρ : Setup X} (hρ : ρ.Good) (rd : Rds Y ρ) (hF : ∀ i j b, Faithful (rd i j b)) (hL : ρ.LatFG)
    (hU : ρ.LevelOf Y) (h : LevelIs Y e U ψ) :
    Nonempty (FullTie hρ (Y := withAll hρ rd hF hL) rd) ∧ LevelIs (withAll hρ rd hF hL) e U ψ ∧
      AllData (withAll hρ rd hF hL) (typedData _) :=
  ⟨⟨fullTieWithAll hρ rd hF hL hU⟩, h, fun _ _ _ _ h => h⟩

theorem types_of_true (C : Formalism.L2.Host.CharFrame D) (h : GlobalTheory.Mem.Top.TypesTrue D.ntypes C.P C.W) :
    GlobalTheory.DimPartsCompare.TameTie D C.W.om := (GlobalTheory.DimPartsCompare.tameTie_of_typesTrue h).2.1

section Cell

variable {ρ : Setup X} {hρ : ρ.Good} {i : X.Tw} {j : Fin D.R.m} {b : Bool} {rd : Rd ρ Y i j b}

theorem rd_injective (T : CellTie hρ Y rd) : Function.Injective rd := by
  refine (injective_iff_map_eq_zero _).2 fun f hf => ?_
  have h0 : ((1 : X.Ok i 0) ⊗ₜ[X.O i] f : X.Ok i 0 ⊗[X.O i] Y.Fm i ((j : ℕ) + 1) b) = 0 :=
    T.injective_rdK 0 (by rw [rdK_tmul, hf, smul_zero, map_zero])
  have : Module.Flat (X.O i) (Y.Fm i ((j : ℕ) + 1) b) :=
    have := IsLocalization.flat (FractionRing (X.O i)) (nonZeroDivisors (X.O i))
    Module.Flat.trans (X.O i) (FractionRing (X.O i)) _
  have hi := Module.Flat.rTensor_preserves_injective_linearMap (M := Y.Fm i ((j : ℕ) + 1) b)
    (Algebra.linearMap (X.O i) (X.Ok i 0)) (X.Ok_inj i 0)
  have h1 : ((1 : X.O i) ⊗ₜ[X.O i] f : X.O i ⊗[X.O i] Y.Fm i ((j : ℕ) + 1) b) = 0 :=
    hi (by rw [LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one, h0, map_zero])
  simpa using congrArg (TensorProduct.lid (X.O i) _) h1

theorem range_th (T : CellTie hρ Y rd) : Set.range (Y.th i ((j : ℕ) + 1) b) =
    {f | ∃ s h P, ρ.IsDatum i j b s h P ∧ rd f = ρ.theta i j b h P} := by
  ext f
  refine ⟨?_, fun ⟨s, h, P, hd, hf⟩ => ?_⟩
  · rintro ⟨d, rfl⟩
    exact ⟨_, _, _, T.dat d, T.th_eq d⟩
  · obtain ⟨d, -, rfl, rfl⟩ := T.dat_onto s h P hd ⟨f, hf⟩
    exact ⟨d, rd_injective T ((T.th_eq d).trans hf.symm)⟩

theorem iUnion_thPsi (T : CellTie hρ Y rd) {k Q φ} (hφ : IntegralHeckeForms.TwOK i k Q φ) : ⋃ d, Y.thPsi i ((j : ℕ) + 1) b k Q φ d =
    {x | ∃ s h P, ρ.IsDatum i j b s h P ∧ ρ.theta i j b h P ∈ Set.range rd ∧ rdK rd hρ k x ∈ ρ.gens i j b k Q φ h P} := by
  ext x
  rw [Set.mem_iUnion]
  refine ⟨fun ⟨d, hd⟩ => ⟨_, _, _, T.dat d, ⟨_, T.th_eq d⟩, (T.thPsi_iff k Q φ hφ d x).1 hd⟩, fun ⟨s, h, P, hd, hr, hx⟩ => ?_⟩
  obtain ⟨d, -, rfl, rfl⟩ := T.dat_onto s h P hd hr
  exact ⟨d, (T.thPsi_iff k Q φ hφ d x).2 hx⟩

end Cell

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} {p : PtAt ex Csz}

theorem RecTies.eSer (h : RecTies p) : GlobalTheory.GLq.ESerTie D := h.types.eSerTie

theorem RecTies.coverField (h : RecTies p) (hc : (R2 p).Char (F2 p)) : GlobalTheory.TwistField.CoverField p.T (R2 p) :=
  GlobalTheory.TwistField.coverField_of_containsRayField _ _ _ _ _ p.T (R2 p) p.fw.laws hc.lev p.qGuard h.rayQ

theorem RecTies.psi_read (h : RecTies p) (w : D.what₂.places.Pl) (hw : D.what₂.muAt w ≠ D.what₂.mu0) (v : PlE D.host)
    (hQ : v ∉ ex.nch.Q w) (hl : v ∉ Formalism.BasicNotions.placesOver D.host.E (D.what₂.places.resChar w)) (B : ValuationSubring D.nd.Om)
    (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) (hB : IsPlaceOver (F := D.host.E) B v) (hσ : IsFrob (F := D.host.E) B (normV v) σ) :
    ∃ y : D.what₂.LL, D.what₂.embLL y = (((p.Tp.psi w).val v)⁻¹ : ℂˣ).1 ∧
      ex.nch.embW w y = algebraMap (ex.nch.Oe w) (FractionRing (ex.nch.Oe w))
        (algebraMap (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) (ex.nch.Oe w)
          ((GlobalTheory.TwistIndex.chosenChar ex.nch w σ : (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w))ˣ) :
            D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w))) := by
  obtain ⟨y, hy⟩ := h.psiVal w hw v (((p.Tp.psi_is w hw).ram v).2 hQ)
  have hy' : D.what₂.embLL y⁻¹ = (((p.Tp.psi w).val v)⁻¹ : ℂˣ).1 := by
    rw [map_inv₀, hy, Units.val_inv_eq_inv_val]
    simp only [Formalism.L2.Host.HChar.valTw, Complex.ofReal_zero, neg_zero, Complex.cpow_zero, mul_one]
  exact ⟨y⁻¹, hy', h.psi w hw v hQ hl B σ hB hσ _ hy'⟩

end Checks

end GlobalTheory.BigOn

end
