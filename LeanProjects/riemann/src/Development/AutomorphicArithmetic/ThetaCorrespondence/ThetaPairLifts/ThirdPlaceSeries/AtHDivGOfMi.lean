import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BkLawEntries
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGood
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SquareIntegrableColumnsTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CountsIrreducibilityConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.Fc.DivLinked
section Read
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Matrix Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Yd : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX}
end Read
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL}
theorem of_built_of_bWit {R : BdP _root_.GlobalTheory.Fc.BundleCondition} {Q : V4.Slot} {κ : Par}
    (h : ∀ (K : Ctx) (q : WPt p.s K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → R _ _ c b)
    {D : D7} {O : Obj D} {c : ℝ} {b : _root_.GlobalTheory.Fc.BundleCondition D O c} (hb : GlobalTheory.Fc.Built Q (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) κ D O c b) : R D O c b := by
  refine GlobalTheory.Fc.Built.ind (R := R) (fun K β c b _ _ hl => ?_) hb
  obtain ⟨q, b', ⟨w⟩, he⟩ := hl
  have := congrArg (fun s : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c => R s.1 s.2.1 c s.2.2) he
  exact cast this.symm (h K q c b' w)
theorem linked_atAll_of_imp {A R : BdP _root_.GlobalTheory.Fc.BundleCondition}
    (h : ∀ (K : Ctx) (q : WPt p.s K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → A _ _ c b → R _ _ c b)
    (hA : _root_.GlobalTheory.Fc.RL.LinkedAt p fun S L => Row S L (AtAll A)) : _root_.GlobalTheory.Fc.RL.LinkedAt p fun S L => Row S L (AtAll R) := by
  obtain ⟨S, hS, hA⟩ := hA
  refine ⟨S, hS, Row.imp hA fun 𝒜 σ s H => ?_⟩
  intro eps Fm hc x hx i
  obtain ⟨κ, -, -, t⟩ := s Fm hc
  exact _root_.GlobalTheory.Fc.DivLinked.of_built_of_bWit (R := fun D O c b => A D O c b → R D O c b) h (t x hx i).1 (H Fm hc x hx i)
section Wit
variable (hC : GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧
  GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay)
  {K : Ctx} {q : WPt p.s K} {c : ℝ} {b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c}
include hC
theorem hDivG_of_mIstar2 (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) (hB : R3.Rw.BkLaw (q.w.D q.Z))
    (hM : (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE) : _root_.GlobalTheory.Fc.R1.DivisorBundleCondition _ _ c b := by
  have h : (fun r : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => (r.B.Q.Rl.toCx3 r.B.Q.F).MIstar2 (r.B.Q.F.eV (r.B.Q.Rl.toCx3 r.B.Q.F).zs) r.B.Q.sEE →
      GlobalTheory.Cp.DivRows3G r.P) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput w.y.y) := fun hM =>
    divisionRows_pairing_vanishes_of_rational_pairing_law hC w.x w.y.intersectionNumber_baseChange hB
      (GlobalTheory.Div.pairing_definite_base_vanish_of_miStar2 _ _ _ _ _ w.x.A3 _ w.x.R w.x.F 1 w.y.intersectionNumber_baseChange.ok w.y.intersectionNumber_baseChange.sep w.x.pins.char
        w.y.intersectionNumber_baseChange.prim w.x.sEE hM)
  rw [← w.y.eq] at h
  exact h hM
end Wit
theorem hDivG_linked_of_mIstar2 (h1 : GlobalTheory.Published.DiscreteSeriesCover) (h2 : GlobalTheory.Published.HarishChandraModules) (h3 : GlobalTheory.Published.CasselmanWallach)
    (h4 : GlobalTheory.Published.HarishChandraFinite) (h5 : GlobalTheory.Published.CuspRapidDecay) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL)
    (hB : ∀ (K : Ctx) (q : WPt p.s K), GlobalTheory.Mem.R3.Rw.BkLaw (q.w.D q.Z))
    (hM : _root_.GlobalTheory.Fc.RL.LinkedAt p fun Q L => Row Q L (AtAll fun _ _ _ (b : _root_.GlobalTheory.Fc.BundleCondition _ _ _) =>
      (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE)) : _root_.GlobalTheory.Fc.RL.LinkedAt p _root_.GlobalTheory.Fc.R1.SlotDivisorCondition :=
  _root_.GlobalTheory.Fc.DivLinked.linked_atAll_of_imp (R := _root_.GlobalTheory.Fc.R1.DivisorBundleCondition) (fun K q _ _ w h => _root_.GlobalTheory.Fc.DivLinked.hDivG_of_mIstar2 ⟨h1, h2, h3, h4, h5⟩ w (hB K q) h) hM
theorem at_hDivG_main_alt : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ (K : Ctx) (q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K), GlobalTheory.Mem.R3.Rw.BkLaw (q.w.D q.Z)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) (fun Q L => Row Q L (AtAll fun _ _ _ (b : _root_.GlobalTheory.Fc.BundleCondition _ _ _) => (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.R1.SlotDivisorCondition :=
  fun _ _ h3 h4 h5 h6 h7 _ _ _ _ hB hM => _root_.GlobalTheory.Fc.DivLinked.hDivG_linked_of_mIstar2 h5 h6 h7 h3 h4 _ hB hM
end GlobalTheory.Fc.DivLinked
end
end
