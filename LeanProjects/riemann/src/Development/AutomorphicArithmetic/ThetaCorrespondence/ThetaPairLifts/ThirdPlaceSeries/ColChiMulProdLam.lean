import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReductionYZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevTraceMemStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LamEqColLamStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TraceChiColFactorStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.FamTraceChiCol
set_option maxHeartbeats 2000000 in
theorem colChi_mul_prod_lam_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → ∀ hy : (y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U, ∃ x : ∀ i, (a.G i).S.P.J, (∀ (i : Fin _) (p q : Fin (I.rec7 l Z).R.k ⊕ Fin ((a.G i).s + 1)) (p' q' : Fin (I.rec7 l Z).R.r),
        p'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ p → q'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ q → ∀ z : 𝓞 (I.rec7 l Z).host.E,
        Ideal.Quotient.mk (a.pl i).1.asIdeal z = (_root_.GlobalTheory.FamTraceChi.reductionYZero_alt W ((show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0)⁻¹ * embA a.d.B.d a.d.B.o κ * (show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0)) (a.pl i)).val p' q' →
        valuation (a.G i).k (((x i : GL (Fin (I.rec7 l Z).R.k ⊕ Fin ((a.G i).s + 1)) (a.G i).k)).val p q - (ofSplit (a.G i).q).pr (z : (I.rec7 l Z).host.E)) < 1) ∧
      (((_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.chi ⟨_, hy⟩ : ℂˣ) : ℂ) * ∏ i, (((a.G i).S.P.lam (x i) : ℂˣ) : ℂ) = 1 := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha haT row col hc κ hκ y hy hU
  have hm := (_root_.GlobalTheory.T.true_geometry_local_data_alt W hA u a ha haT row col hc κ hκ y hy).1 hU
  obtain ⟨hg, -⟩ := _root_.GlobalTheory.FamTraceChi.rChi_eq_lvP_chi_of_mem W hm
  choose x hx using ((ha.tie row col).2.lev _).1.1 hg
  refine ⟨x, hx, ?_⟩
  rw [Finset.prod_congr rfl (fun i _ => _root_.GlobalTheory.T.true_geometry_final_scalar_alt W hA u a ha haT row col hc κ hκ y hy hU i (x i) (hx i))]
  exact _root_.GlobalTheory.T.true_geometry_class_relation_alt W hA u a ⟨_, hU⟩
end GlobalTheory.FamTraceChiCol
end
end
