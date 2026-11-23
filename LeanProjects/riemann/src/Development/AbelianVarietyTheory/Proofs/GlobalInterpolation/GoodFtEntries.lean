import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OExt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RootsOfUnityRingLeWittIntegers
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowTruthOfLabelTieStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConstructedSpectralObjectsIrreducibilityConditioStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsTerAlt

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM

namespace GlobalTheory.Fc.LabLinked

def Ties (D : D7) : Prop :=
  ∃ (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : Formalism.L2.SG.RowDict.GoodOp X)
    (ι : D.s.HH ≃ₗᵢ[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X),
    Formalism.MainNotions.S.AutTie D X.B X.pl ∧ Formalism.L2.SG.RowDict.RowDictTie X G ι ∧ GlobalTheory.LabPin.LabTie X ι

def GenPin {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (a : NAt hL D cf nch tp) : Prop :=
  ∀ k, a.nt.A.grp.ζ k = @GlobalTheory.GLq.LabelDatum.gen _ ⟨a.nt.D.host.g_prime k⟩
    (@GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩)

set_option maxHeartbeats 2000000 in

theorem typeLab_of_gen (hG : GlobalTheory.GLq.Green) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) (hDZ : GlobalTheory.Published.DepthZeroInertia)
    {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (a : NAt hL D cf nch tp)
    (hl : GlobalTheory.SerSys.LabTie D fun k => @GlobalTheory.Mem.TypePl.labDat (D.host.g k) ⟨D.host.g_prime k⟩) (hp : GenPin a)
    (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (hrep : HEq a.nt.rep rep) : GlobalTheory.LabPin.TypeLab D rep := by
  have e : ∀ (D' : D7), D' = withLoc a.nt.L →
      (GlobalTheory.SerSys.LabTie D' fun k => @GlobalTheory.Mem.TypePl.labDat (D'.host.g k) ⟨D'.host.g_prime k⟩) →
      ∀ rep' : D'.what₂.FT → Formalism.L2.NG.FinTyp D'.host.E D'.R.r, HEq a.nt.rep rep' → GlobalTheory.LabPin.TypeLab D' rep' := by
    rintro _ rfl hl' rep' hr
    obtain rfl := eq_of_heq hr
    refine GlobalTheory.T.rowTruth_of_labelTie hG hZ hDZ hL a.nt.D a.nt.A.wdT a.nt.A.row a.nt.rep
      (fun k => @GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩) a.nt.A.lab a.nt.row a.depth hl' ?_
    intro k v
    refine ⟨a.nt.A.grp.kv k v, ?_⟩
    rw [← hp k]
    exact a.nt.A.grp.tg_tame k v
  exact e D a.nt.eq hl rep hrep

section Rows

open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.NX

set_option maxHeartbeats 1000000 in

theorem ties_at_rows (hG : GlobalTheory.GLq.Green) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) (hDZ : GlobalTheory.Published.DepthZeroInertia)
    {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {hL : GlobalTheory.Published.LocalLanglandsGL} {cf : CharFrame D} {nch : NChoice D}
    {tp : TupTied D cf nch} {a : NAt hL D cf nch tp} {R : RealDat3 D A3 Ks} {F : Face3 D A3} {cG : G0 R.Pg D.R.r ≃* G0g D.nd}
    {X0 : BaseLevelRowSide D} {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0} (r : NRow a R F cG Y) {F0 : ∀ u, Formalism.L2.Forms.Forms0 D u}
    (s : SAt R.toRealDat F.lv2 Y.eE F0)
    (hl : GlobalTheory.SerSys.LabTie D fun k => @GlobalTheory.Mem.TypePl.labDat (D.host.g k) ⟨D.host.g_prime k⟩) (hp : GenPin a)
    (hg : GoodFTAll D) : Ties D := by
  have hR := GlobalTheory.Mem.R3.RowFrameParts.main D G Pl0 I0 T A3 Ks R.toRealDat F.lv2 X0 Y
  have hT := typeLab_of_gen hG hZ hDZ a hl hp _ r.rep_eq
  exact ⟨s.P.X, s.P.G, s.S.hI.eHH,
    GlobalTheory.T.constructedSpectralObjects_irreducibilityConditions D G Pl0 T A3.A Ks R.toRealDat F.lv2 Y.eE F0 s Y.PY Y.hF
      (fun σ : D.what₂.FT => principalLevelFrame.rowRepR R.θ (Y.eFT σ)) hR.1 hR.2 hT hg⟩

end Rows

theorem lab_of_rows {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0) :
    GlobalTheory.SerSys.LabTie (w.D Z) fun k => @GlobalTheory.Mem.TypePl.labDat ((w.D Z).host.g k) ⟨(w.D Z).host.g_prime k⟩ :=
  fun k => ⟨(t.grp.teich k).symm, t.grp.ser k⟩

set_option maxHeartbeats 1000000 in

theorem ties_at_wit (hG : GlobalTheory.GLq.Green) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) (hDZ : GlobalTheory.Published.DepthZeroInertia)
    {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL} {K : Ctx} (q : WPt p.s K) (hp : GenPin q.core.a)
    (hg : GoodFTAll (q.w.D q.Z)) : Ties (q.w.D q.Z) :=
  ties_at_rows hG hZ hDZ (D := (q.w.st q.Z).toD7) q.core.row q.sat (lab_of_rows q.x.what₂) hp hg

theorem ties_of_built (hG : GlobalTheory.GLq.Green) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) (hDZ : GlobalTheory.Published.DepthZeroInertia)
    {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL} (hp : ∀ (K : Ctx) (q : WPt p.s K), GenPin q.core.a) {Q : V4.Slot} {κ : Par}
    {D : D7} {O : Obj D} {c : ℝ} {b : Bundle D O c} (hb : Built Q (IsLinked p) κ D O c b) : GoodFTAll D → Ties D := by
  refine Built.ind (R := fun D _ _ _ => GoodFTAll D → Ties D) ?_ hb
  rintro K β c b - - ⟨q, b', -, e⟩
  have e1 : β.D = q.w.D q.Z := congrArg Sigma.fst e
  show GoodFTAll β.D → Ties β.D
  rw [e1]
  exact ties_at_wit hG hZ hDZ q (hp K q)

theorem row_lab_of_good : GlobalTheory.GLq.Green → GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.DepthZeroInertia → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → ∀ k, c.a.nt.A.grp.ζ k = @GlobalTheory.GLq.LabelDatum.gen _ ⟨c.a.nt.D.host.g_prime k⟩ (@GlobalTheory.Mem.TypePl.labDat (c.a.nt.D.host.g k) ⟨c.a.nt.D.host.g_prime k⟩)) → RL.At (prmR N S Γ) (fun Q Lk => Row Q Lk (AtAll fun D _ _ _ => GoodFTAll D)) → RL.At (prmR N S Γ) RL.LabelCondition := by
  intro hG hZ hDZ hL N S Γ hN ⟨R, hR, hrow⟩
  refine ⟨R, hR, hrow.imp fun 𝒜 σ s hA eps Fm hc x hx i => ?_⟩
  obtain ⟨κ, -, -, t⟩ := s Fm hc
  exact ties_of_built hG hZ hDZ (p := prmR N S Γ) (fun K q => hN _ _ _ _ _ _ _ _ _ _ _ _ _ q.x.nx.2) (t x hx i).1 (hA Fm hc x hx i)

theorem row_lab_ev_of_good (hG : GlobalTheory.GLq.Green) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) (hDZ : GlobalTheory.Published.DepthZeroInertia)
    {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL} (hp : ∀ (K : Ctx) (q : WPt p.s K), GenPin q.core.a) :
    RL.At p RL.GoodReductionCondition → RL.At p fun Q Lk => Row Q Lk (Ind.EvW (Bd := Bundle) fun D _ _ _ => Ties D) := by
  intro ⟨R, hR, hrow⟩
  refine ⟨R, hR, hrow.imp fun 𝒜 σ s hA => Closed.imp hA fun Fm _ _ h hc => ?_⟩
  obtain ⟨x0, h⟩ := h hc
  obtain ⟨κ, -, -, t⟩ := s Fm (w3_a hc)
  exact ⟨x0, fun x hx h0 i => ties_of_built hG hZ hDZ hp (t x hx i).1 (h x hx h0 i)⟩

theorem row_lab_labelCondition_of_localLanglands (hG : GlobalTheory.GLq.Green) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) (hDZ : GlobalTheory.Published.DepthZeroInertia)
    (hL : GlobalTheory.Published.LocalLanglandsGL) (S : SExt) (Γ : GeoP) :
    RL.At (prmR (NE hL) S Γ) (fun Q Lk => Row Q Lk (AtAll fun D _ _ _ => GoodFTAll D)) → RL.At (prmR (NE hL) S Γ) RL.LabelCondition :=
  row_lab_of_good hG hZ hDZ hL (NE hL) S Γ fun _ _ _ _ _ _ _ _ _ _ _ _ _ m => m.zeta

theorem row_lab_of_layer : GlobalTheory.GLq.Green → GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.DepthZeroInertia → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (GlobalTheory.HeightCounting.Up.NEb hL K B f T w Z Wt p0 t nch n xd c)) → RL.At (prmR N S Γ) (fun Q L => Row Q L (AtAll fun D _ _ (_ : Bundle _ _ _) => Formalism.BasicNotions.GoodFTAll D)) → RL.At (prmR N S Γ) RL.LabelCondition :=
  fun hG hZ hDZ hL N S Γ hN =>
    row_lab_of_good hG hZ hDZ hL N S Γ fun K B f T w Z Wt p0 t nch n xd c m =>
      (hN K B f T w Z Wt p0 t nch n xd c m).elim fun e => e.1.zeta

end GlobalTheory.Fc.LabLinked
