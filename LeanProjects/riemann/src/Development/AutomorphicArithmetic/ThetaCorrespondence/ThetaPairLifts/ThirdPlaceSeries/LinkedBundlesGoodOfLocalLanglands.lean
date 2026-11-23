import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinkedBundlesGoodOfLocalLanglandsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGood
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGoodRec
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OPin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OpinAtMemStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalSeriesConcreteOfDzSwap
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
namespace GlobalTheory.Fc.GoodLinked
section Layer
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 4000000 in
theorem goodFTAll_at_members_of_depthZero (h1 : GlobalTheory.GLq.Green) (h2 : GlobalTheory.Published.ZelevinskyPolynomialRing) :
    ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists,
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => GoodFTAll (w.D Z) := by
  intro hL
  have hA := _root_.GlobalTheory.T.coefficient_duty_pin_at_each_member hL
  have hO := GlobalTheory.TypeVecConj.typeVec
  refine EvG.imp (EvG.inter hA hO) fun K _ _ _ _ h => ?_
  refine large₂.imp (large₂.inter h.1 h.2) fun B f T _ g => ?_
  intro hK w Z Wt p0 t nch n xd c _ _ hpin
  have hop := g.1 hK w Z Wt p0 t nch n xd c ‹_› ‹_› hpin
  have hrow := g.2 hK w hpin Z Wt t.hX t.r.z p0 t.r.Y t.r.intersectionNumber_baseChange t.exAt t.inGeo t.grp t.grpAt
  refine _root_.UpperTheory.Lit.Dz.nonGaloisTwistType h1 h2 hL (w.D Z) _ nch n.tp c.a hop ?_
  have key : ∀ (D' : D7) (_ : D' = withLoc c.a.nt.L) (r' : D'.what₂.FT → NG.FinTyp D'.host.E D'.R.r), HEq c.a.nt.rep r' →
      (∀ (I : GlobalTheory.TypeRec.Ident D') cp, GlobalTheory.TypeRec.IsComp I r' cp → ∀ σ, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
        (ρ : Representation ℂ (G0g D'.nd) V) (W : Submodule ℂ V) (x : V),
        (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom D' k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧ (∀ a, ρ.asAlgebraHom a x ∈ W) ∧
        ρ.asAlgebraHom D'.ntypes.e0 x = x) →
      ∀ (I : GlobalTheory.TypeRec.Ident c.a.nt.D) cp, GlobalTheory.TypeRec.IsComp I c.a.nt.rep cp → ∀ σ, ∃ (V : Type) (_ : AddCommGroup V)
        (_ : Module ℂ V) (ρ : Representation ℂ (G0g c.a.nt.D.nd) V) (W : Submodule ℂ V) (x : V),
        (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom c.a.nt.D k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧
        (∀ b, ρ.asAlgebraHom b x ∈ W) ∧ ρ.asAlgebraHom c.a.nt.D.ntypes.e0 x = x := by
    rintro _ rfl r' hr h
    have e : c.a.nt.rep = r' := eq_of_heq hr
    rw [e]
    intro I cp hc σ
    exact h ⟨I.i, I.cont⟩ cp hc σ
  exact key _ c.a.nt.eq _ c.row.rep_eq hrow
end Layer
end GlobalTheory.Fc.GoodLinked
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.Fc.GoodLinked
set_option maxHeartbeats 2000000 in
theorem largeBasePropertyG_goodRec_alt_alt (h1 : GlobalTheory.GLq.Green) (h2 : GlobalTheory.Published.ZelevinskyPolynomialRing)
    (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP)
    (hN : ∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c →
      Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) :
    GroupRetwisting.LargeBaseConditionG KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) GoodRec := by
  refine GlobalTheory.Mem.Top.EvG.imp (_root_.GlobalTheory.Fc.GoodLinked.goodFTAll_at_members_of_depthZero h1 h2 hL) fun K _ _ _ _ H => H.imp fun B f T _ t k C W V S' N G c q => ?_
  obtain ⟨w, Z, c', ⟨b, _⟩, e⟩ := q
  have key : ∀ x : Σ (C : Cols B) (Y : TC.Later B C), V4.Core K ⟨B, C, Y.W, Y.V, Y.S, Y.N, Y.G⟩ f T,
      x = ⟨w.C, Z, c'⟩ → Formalism.BasicNotions.GoodFTAll (⟨B, x.1, x.2.1.W, x.2.1.V, x.2.1.S, x.2.1.N, x.2.1.G⟩ : Stages).toD7 := by
    rintro _ rfl
    exact t k w Z c'.Wt c'.O.p0 b.what₂ c'.O.nch b.n c'.O.xd b.nx.1 ((hN _ _ _ _ _ _ _ _ _ _ _ _ _ b.nx.2).map Prod.fst) ⟨b.rx⟩ b.pin
  exact key _ e
theorem linkedAt_goodFTAll : GlobalTheory.GLq.Green → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP),
    (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c →
      Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) →
    _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) fun Q L => Row Q L (AtAll fun D _ _ (_ : _root_.GlobalTheory.Fc.BundleCondition _ _ _) => Formalism.BasicNotions.GoodFTAll D) :=
  fun h1 h2 hL N S Γ hN => LgModel.rowL_of_good (_root_.GlobalTheory.Fc.GoodLinked.largeBasePropertyG_goodRec_alt_alt h1 h2 hL N S Γ hN) (_root_.GlobalTheory.Fc.GoodLinked.row_goodRec_alt _)
theorem row_good_alt_alt : GlobalTheory.GLq.Green → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP),
    (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c →
      Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) →
    _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) (fun Q L => Row Q L (AtAll fun D _ _ (_ : _root_.GlobalTheory.Fc.BundleCondition _ _ _) => Formalism.BasicNotions.GoodFTAll D)) ∧
      _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.RowGoodnessCondition := by
  intro h1 h2 hL N S Γ hN
  refine ⟨_root_.GlobalTheory.Fc.GoodLinked.linkedAt_goodFTAll h1 h2 hL N S Γ hN, ?_⟩
  obtain ⟨R, hR, h⟩ := _root_.GlobalTheory.Fc.GoodLinked.linkedAt_goodFTAll h1 h2 hL N S Γ hN
  refine ⟨R, hR, h.imp fun _ _ _ key => ?_⟩
  exact ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ hc => Ind.ev_of_atAll key Fm (w3_a hc)⟩⟩
end GlobalTheory.Fc.GoodLinked
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linked_bundles_good_of_local_langlands_alt_alt : GlobalTheory.GLq.Green → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) (fun Q L => Row Q L (AtAll fun D _ _ (_ : _root_.GlobalTheory.Fc.BundleCondition _ _ _) => Formalism.BasicNotions.GoodFTAll D)) ∧ _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.RowGoodnessCondition := by
  first | exact @_root_.GlobalTheory.Fc.GoodLinked.row_good_alt_alt | exact _root_.GlobalTheory.Fc.GoodLinked.row_good_alt_alt | (intros; apply _root_.GlobalTheory.Fc.GoodLinked.row_good_alt_alt <;> assumption)
end
end
