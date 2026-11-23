import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinkedBundlePropertyAfterLargeBaseCoreProperty
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.NRows.AtPt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
  GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Fc NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
def OverNEAlt (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) : Prop :=
  ∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.defaultExtension hL K B f T w Z Wt p0 t nch n xd c)
def membershipLocation (P : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL) : V4.Slot := fun K X f T _ =>
  ∀ w Z Wt p0 t nch n xd c, Nonempty (_root_.GlobalTheory.HeightCounting.defaultExtension hL K X.B f T w Z Wt p0 t nch n xd c) → Nonempty (RXs t) → ColPin w →
    P K X.B f T w Z Wt p0 t nch n c
abbrev WitnessAtPoint (P : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL) {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : WPt p.s K) : Prop :=
  P K q.B q.f q.T q.w q.Z q.x.Wt _ q.x.what₂ _ q.x.n q.core_data_of_point
theorem lgSlotG_memSlot' {P : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL} (h : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL P) (Q : V4.Slot) : LargeBaseConditionG KPx Q (_root_.GlobalTheory.NRows.AtPt.membershipLocation P) :=
  EvG.imp h fun _ _ _ _ _ hK => large₂.imp hK fun _ _ _ _ H kp _ _ _ _ _ _ _ _ => H kp
section
variable {N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL} {S : SExt} {Γ : GeoP} {P : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL}
theorem exists_wPt_entC_atWit_of_heq (hN : _root_.GlobalTheory.NRows.AtPt.OverNEAlt N) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {D : D7}
    (hP : ∀ w Z Wt p0 t nch n xd c, Nonempty (_root_.GlobalTheory.HeightCounting.defaultExtension hL K B f T w Z Wt p0 t nch n xd c) → Nonempty (RXs t) → ColPin w →
      P K B f T w Z Wt p0 t nch n c)
    (e : w.D Z = D) (O : Obj D) {O' : Obj2 (w.D Z)} (hO : HEq (ofObj O) O') (x : Wit (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K w Z O') (hx : EntC x.ker) :
    ∃ q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K, q.Is D O ∧ EntC q.x.ker ∧ _root_.GlobalTheory.NRows.AtPt.WitnessAtPoint (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) P q := by
  subst e
  obtain rfl := eq_of_heq hO
  exact ⟨⟨B, f, T, w, Z, O, x⟩, rfl, hx, hP w Z _ _ _ _ _ _ x.nx.1 (hN _ _ _ _ _ _ _ _ _ _ _ _ _ x.nx.2) ⟨x.rx⟩ x.pin⟩
set_option maxHeartbeats 2000000 in
theorem exists_wit_pt_alt (hN : _root_.GlobalTheory.NRows.AtPt.OverNEAlt N) (H : WitMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {Z : w.Lt}
    (hP : ∀ w Z Wt p0 t nch n xd c, Nonempty (_root_.GlobalTheory.HeightCounting.defaultExtension hL K B f T w Z Wt p0 t nch n xd c) → Nonempty (RXs t) → ColPin w →
      P K B f T w Z Wt p0 t nch n c)
    {O : Obj2 (w.D Z)} (x : Wit (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K w Z O) (hx : EntC x.ker) (Y : Lay (w.D Z)) (hY : layObj Y = O) (p : LedPart K.C Y) :
    ∃ q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K, q.Is p.pt.D (Obj.ofPt p.pt) ∧ EntC q.x.ker ∧ _root_.GlobalTheory.NRows.AtPt.WitnessAtPoint (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) P q := by
  obtain ⟨y, hy⟩ := H K B f T w Z O x (nPrime p.L) p.ht hx
  exact _root_.GlobalTheory.NRows.AtPt.exists_wPt_entC_atWit_of_heq hN hP (Db.D_setDivZ w Z (nPrime p.L) p.ht) (Obj.ofPt p.pt)
    (hY ▸ heq_of_eq (pointObj_pt p)) y hy
set_option maxHeartbeats 2000000 in
theorem exists_wPt_entC_atWit (hN : _root_.GlobalTheory.NRows.AtPt.OverNEAlt N) (H : WitMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) {K : Ctx} (β : BPt K)
    (hβ : β.Is (sAnd (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (_root_.GlobalTheory.NRows.AtPt.membershipLocation P))) :
    ∃ q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K, q.Is β.D β.O ∧ EntC q.x.ker ∧ _root_.GlobalTheory.NRows.AtPt.WitnessAtPoint (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) P q :=
  positionOf_ind (P := GoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (R := fun K X f T c => _root_.GlobalTheory.NRows.AtPt.membershipLocation P K X f T c →
      ∀ (Y : Lay X.toD7) (_ : layObj Y = c.O) (p : LedPart K.C Y),
      ∃ q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K, q.Is p.pt.D (Obj.ofPt p.pt) ∧ EntC q.x.ker ∧ _root_.GlobalTheory.NRows.AtPt.WitnessAtPoint (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) P q)
    (fun _ _ _ _ _ _ _ g hP => g.1.elim fun b hb => _root_.GlobalTheory.NRows.AtPt.exists_wit_pt_alt hN H hP (b.wit g.2) hb)
    hβ.1 hβ.2 β.Y β.hY β.p
theorem memSlot_entry_of_atWit (hN : _root_.GlobalTheory.NRows.AtPt.OverNEAlt N) (H : WitMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) {r : ∀ D : D7, Obj D → Prop}
    (hr : ∀ K (q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K), EntC q.x.ker → _root_.GlobalTheory.NRows.AtPt.WitnessAtPoint (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) P q → r (q.w.D q.Z) q.O) {Bd : BdT} (Lk : LkT Bd) :
    RowE (sAnd (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (_root_.GlobalTheory.NRows.AtPt.membershipLocation P)) Lk fun _ D O _ _ => r D O :=
  RowE.of_all fun _ K β _ _ _ hβ _ => let ⟨q, a, b, c⟩ := _root_.GlobalTheory.NRows.AtPt.exists_wPt_entC_atWit hN H β hβ; of_is a (hr K q b c)
end
theorem lg1_entry_of_atWit {N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL} {S : SExt} {Γ : GeoP} {P : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL} (h : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL P) (hN : _root_.GlobalTheory.NRows.AtPt.OverNEAlt N)
    (H : WitMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) {r : ∀ D : D7, Obj D → Prop}
    (hr : ∀ K (q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K), EntC q.x.ker → _root_.GlobalTheory.NRows.AtPt.WitnessAtPoint (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) P q → r (q.w.D q.Z) q.O) {Bd : BdT} (Lk : LkT Bd) :
    Lg1 KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) fun U => RowE U Lk fun _ D O _ _ => r D O :=
  linkedBundleProperty_after_largeBaseCoreProperty (_root_.GlobalTheory.NRows.AtPt.lgSlotG_memSlot' h _) (_root_.GlobalTheory.NRows.AtPt.memSlot_entry_of_atWit hN H hr Lk)
end GlobalTheory.NRows.AtPt
end
end
