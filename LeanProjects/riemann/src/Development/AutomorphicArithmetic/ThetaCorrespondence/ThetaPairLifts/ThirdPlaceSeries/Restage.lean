import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideDataOverSetLevels
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RestageCopyStatement
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
noncomputable section
namespace GlobalTheory.HeightCounting.Up
open GlobalTheory.Mem.R3.Tr in
theorem restage_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x) (N : TwNew (Dof x)), Nonempty (SideB N.toD7 (N.cf (cfOf x)) (N.row l.a.A.row) (lowAll (Dof x)) l.Pq (N.rat l.rat.S) l.rat.In.hL l.rat.In.eig l.rat.In.θ) → (∀ i, l.rat.In.Sb ⊆ N.tw.S0 i) → (∀ i, OverSet (Dof x) (N.tw.S0 i) (insert (N.tw.l i) (lowAll (Dof x)))) → ∀ G : GlobalTheory.ChiGrid.GridData x.m.z.R.toRealDat.toLevCh ⟨1, cDep, K.s.b⟩, GlobalTheory.BigTop.Fun.FieldHas G (embLL0 (Dof x)) → (GlobalTheory.BigTop.Fun.lamOf G).Ok → (GlobalTheory.BigTop.Fun.lamOf G).C = cfOf x → (GlobalTheory.BigTop.Fun.lamOf G).q0 = AbsolutelyIrreducibleSpan.q0 (Dof x) → GlobalTheory.LamTie.IsLamTieFull N.tw (GlobalTheory.BigTop.Fun.lamOf G) → ∃ x' : St P, Nonempty (_root_.GlobalTheory.HeightCounting.Up.FirstIntermediateLevel hL x') ∧ ListSt cDep x' := by
  intro hL cDep K B f T w P x l N hSB hSb hS0 G hF hOk hC hq0 hTie
  obtain ⟨x', l', ho, hLc, hrow, hPq, hS, hSb', hhL, heig, hθ⟩ := _root_.GlobalTheory.T.twisted_state_transport_heq' hL x l N
  obtain ⟨o', fits', G_eq', etaF', bk', m', copy', coh', s', r', pin'⟩ := x'
  dsimp only at ho
  subst ho
  obtain ⟨sb⟩ := hSB
  have eL : m'.z.R.toRealDat.toLevCh = (by with_unfolding_all exact ((levCh (a := x.o.Z) (oTw x N).Z x.m.z.R.toRealDat.toLevCh) :)) := eq_of_heq hLc
  have hPin : ListPin N.toD7 ((by with_unfolding_all exact ((levCh (a := x.o.Z) (oTw x N).Z x.m.z.R.toRealDat.toLevCh) :)) :
      Formalism.IndefR.Links.LevCh N.toD7 _) cDep K.s.b :=
    ⟨(by with_unfolding_all exact ((GlobalTheory.Mem.GridMove.gdC (a := x.o.Z) (oTw x N).Z G) :)), ⟨(by with_unfolding_all exact (hF.values :)), (by with_unfolding_all exact (hF.roots :))⟩, (by with_unfolding_all exact (hTie :))⟩
  have hLam : ∃ Z : GlobalTheory.LamTie.LamDat N.toD7, Z.Ok ∧ Z.Teich ∧ Z.C = N.cf (cfOf x) ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 N.toD7 ∧
      GlobalTheory.LamTie.IsLamTieFull N.toD7.ntw Z :=
    ⟨(by with_unfolding_all exact ((GlobalTheory.BigTop.Fun.lamOf (GlobalTheory.Mem.GridMove.gdC (a := x.o.Z) (oTw x N).Z G)) :)), ⟨(by with_unfolding_all exact (hOk.places :)), (by with_unfolding_all exact (hOk.aux :)), (by with_unfolding_all exact (hOk.big :))⟩,
      (by with_unfolding_all exact ((GlobalTheory.BigTop.Fun.lamOf_teich (GlobalTheory.Mem.GridMove.gdC (a := x.o.Z) (oTw x N).Z G)) :)),
      (by with_unfolding_all exact ((congrArg (TwNew.cf N) hC) :)), (by with_unfolding_all exact (hq0 :)), (by with_unfolding_all exact (hTie :))⟩
  refine ⟨⟨oTw x N, fits', G_eq', etaF', bk', m', copy', coh', s', r', pin'⟩, ⟨{ toLI := l', b := ?_ }⟩, ?_⟩
  · refine ⟨sideB_congr rfl (eq_of_heq hrow).symm rfl (eq_of_heq hPq).symm (eq_of_heq hS).symm hhL.symm
      (eq_of_heq heig).symm (eq_of_heq hθ).symm sb, fun i => (eq_of_heq hSb') ▸ hSb i, fun i => hS0 i, hLam⟩
  · show ListPin _ m'.z.R.toRealDat.toLevCh cDep K.s.b
    rw [eL]
    exact hPin
end GlobalTheory.HeightCounting.Up
end
end
