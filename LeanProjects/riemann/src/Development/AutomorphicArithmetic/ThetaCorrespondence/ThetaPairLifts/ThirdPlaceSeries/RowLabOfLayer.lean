import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodFtEntriesStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGood
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GenPin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalSeriesConcreteOfDzSwap
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.HeightCounting
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
namespace GlobalTheory.Fc.LabLinked
set_option maxHeartbeats 2000000 in
theorem typeLab_of_gen_alt_alt (hG : GlobalTheory.GLq.Green) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing)
    {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf nch tp)
    (hl : GlobalTheory.SerSys.LabTie D fun k => @GlobalTheory.Mem.TypePl.labDat (D.host.g k) ⟨D.host.g_prime k⟩) (hp : _root_.GlobalTheory.Fc.LabLinked.GenPinAlt a)
    (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (hrep : HEq a.nt.rep rep) : GlobalTheory.LabPin.TypeLab D rep := by
  have e : ∀ (D' : D7), D' = withLoc a.nt.L →
      (GlobalTheory.SerSys.LabTie D' fun k => @GlobalTheory.Mem.TypePl.labDat (D'.host.g k) ⟨D'.host.g_prime k⟩) →
      ∀ rep' : D'.what₂.FT → Formalism.L2.NG.FinTyp D'.host.E D'.R.r, HEq a.nt.rep rep' → GlobalTheory.LabPin.TypeLab D' rep' := by
    rintro _ rfl hl' rep' hr
    obtain rfl := eq_of_heq hr
    refine _root_.UpperTheory.Lit.Dz.localBesselMultiplicityOne hG hZ hL a.nt.D a.nt.A.wdT a.nt.A.row a.nt.rep
      (fun k => @GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩) a.nt.A.lab a.nt.row a.depth hl' ?_
    intro k v
    refine ⟨a.nt.A.grp.kv k v, ?_⟩
    rw [← hp k]
    exact a.nt.A.grp.tg_tame k v
  exact e D a.nt.eq hl rep hrep
section Rows
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.NX
set_option maxHeartbeats 1000000 in
theorem ties_of_nAtData_real (hG : GlobalTheory.GLq.Green) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing)
    {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {cf : CharFrame D} {nch : NChoice D}
    {tp : TupTied D cf nch} {a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf nch tp} {R : RealDat3 D A3 Ks} {F : Face3 D A3} {cG : G0 R.Pg D.R.r ≃* G0g D.nd}
    {X0 : BaseLevelRowSide D} {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0} (r : _root_.GlobalTheory.Mem.Top.Bl.NormRealisationData a R F cG Y) {F0 : ∀ u, Formalism.L2.Forms.Forms0 D u}
    (s : SAt R.toRealDat F.lv2 Y.eE F0)
    (hl : GlobalTheory.SerSys.LabTie D fun k => @GlobalTheory.Mem.TypePl.labDat (D.host.g k) ⟨D.host.g_prime k⟩) (hp : _root_.GlobalTheory.Fc.LabLinked.GenPinAlt a)
    (hg : GoodFTAll D) : Ties D := by
  have hR := GlobalTheory.Mem.R3.RowFrameParts.main D G Pl0 I0 T A3 Ks R.toRealDat F.lv2 X0 Y
  have hT := _root_.GlobalTheory.Fc.LabLinked.typeLab_of_gen_alt_alt hG hZ a hl hp _ r.rep_eq
  exact ⟨s.P.X, s.P.G, s.S.hI.eHH,
    GlobalTheory.T.constructedSpectralObjects_irreducibilityConditions D G Pl0 T A3.A Ks R.toRealDat F.lv2 Y.eE F0 s Y.PY Y.hF
      (fun σ : D.what₂.FT => principalLevelFrame.rowRepR R.θ (Y.eFT σ)) hR.1 hR.2 hT hg⟩
end Rows
set_option maxHeartbeats 1000000 in
theorem ties_of_genPin_goodFTAll' (hG : GlobalTheory.GLq.Green) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing)
    {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : WPt p.s K) (hp : _root_.GlobalTheory.Fc.LabLinked.GenPinAlt q.core_data_of_point.a)
    (hg : GoodFTAll (q.w.D q.Z)) : Ties (q.w.D q.Z) :=
  _root_.GlobalTheory.Fc.LabLinked.ties_of_nAtData_real hG hZ (D := (q.w.st q.Z).toD7) q.core_data_of_point.row q.saturationAtWeightedPoint (lab_of_rows q.x.what₂) hp hg
theorem ties_of_built_genPin (hG : GlobalTheory.GLq.Green) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing)
    {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} (hp : ∀ (K : Ctx) (q : WPt p.s K), _root_.GlobalTheory.Fc.LabLinked.GenPinAlt q.core_data_of_point.a) {Q : V4.Slot} {κ : Par}
    {D : D7} {O : Obj D} {c : ℝ} {b : _root_.GlobalTheory.Fc.BundleCondition D O c} (hb : Built Q (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) κ D O c b) : GoodFTAll D → Ties D := by
  refine Built.ind (R := fun D _ _ _ => GoodFTAll D → Ties D) ?_ hb
  rintro K β c b - - ⟨q, b', -, e⟩
  have e1 : β.D = q.w.D q.Z := congrArg Sigma.fst e
  show GoodFTAll β.D → Ties β.D
  rw [e1]
  exact _root_.GlobalTheory.Fc.LabLinked.ties_of_genPin_goodFTAll' hG hZ q (hp K q)
theorem row_lab_of_good_alt_alt : GlobalTheory.GLq.Green → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → ∀ k, c.a.nt.A.grp.ζ k = @GlobalTheory.GLq.LabelDatum.gen _ ⟨c.a.nt.D.host.g_prime k⟩ (@GlobalTheory.Mem.TypePl.labDat (c.a.nt.D.host.g k) ⟨c.a.nt.D.host.g_prime k⟩)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) (fun Q Lk => Row Q Lk (AtAll fun D _ _ _ => GoodFTAll D)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.RowLabelCondition := by
  intro hG hZ hL N S Γ hN ⟨R, hR, hrow⟩
  refine ⟨R, hR, hrow.imp fun 𝒜 σ s hA eps Fm hc x hx i => ?_⟩
  obtain ⟨κ, -, -, t⟩ := s Fm hc
  exact _root_.GlobalTheory.Fc.LabLinked.ties_of_built_genPin hG hZ (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) (fun K q => hN _ _ _ _ _ _ _ _ _ _ _ _ _ q.x.nx.2) (t x hx i).1 (hA Fm hc x hx i)
theorem row_lab_of_layer_alt_alt : GlobalTheory.GLq.Green → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) (fun Q L => Row Q L (AtAll fun D _ _ (_ : _root_.GlobalTheory.Fc.BundleCondition _ _ _) => Formalism.BasicNotions.GoodFTAll D)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.RowLabelCondition :=
  fun hG hZ hL N S Γ hN =>
    _root_.GlobalTheory.Fc.LabLinked.row_lab_of_good_alt_alt hG hZ hL N S Γ fun K B f T w Z Wt p0 t nch n xd c m =>
      (hN K B f T w Z Wt p0 t nch n xd c m).elim fun e => e.1.zeta
end GlobalTheory.Fc.LabLinked
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_ft_entries_alt_alt : GlobalTheory.GLq.Green → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) (fun Q L => Row Q L (AtAll fun D _ _ (_ : _root_.GlobalTheory.Fc.BundleCondition _ _ _) => Formalism.BasicNotions.GoodFTAll D)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.RowLabelCondition := by
  first | exact @_root_.GlobalTheory.Fc.LabLinked.row_lab_of_layer_alt_alt | exact _root_.GlobalTheory.Fc.LabLinked.row_lab_of_layer_alt_alt | (intros; apply _root_.GlobalTheory.Fc.LabLinked.row_lab_of_layer_alt_alt <;> assumption)
end
end
