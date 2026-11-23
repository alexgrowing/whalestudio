import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMove
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove GlobalTheory.HeightCounting.SideCopy GlobalTheory.Mem.R3.Tr
namespace GlobalTheory.HeightCounting.SerGlue
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B}
  {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'}
theorem exists_move_alt (hKP : KPx B' f') (hF : Forced K B' T') (hS' : Start K B' f' T' w') (hO : K.Over B'.toPre)
    (hB : ∀ X : Stages, K.Over X.B.toPre → Formalism.IndefR.Links.HostHyp X.toD7 ∧ 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV)
    (hE : Enl B B') (hf : HEq f' f) (hSt : Start K B f T w) (hpx : HEq w'.px w.px) (hsel : HEq w'.I.sel w.I.sel)
    (hJ : HEq w'.I.J w.I.J) (hδ : HEq w'.δ w.δ) (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x) (hExt : Ext P.z P'.z) (x' : St P')
    (hG : SameGal (Dof x) (Dof x')) (N : TwNew (Dof x')) {ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL}
    {e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0} (hN : CopyN (Dof x) N ι e) (x'' : St P') (l'' : _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x'') (ho : x''.o = oTw x' N) :
    ∃ (ι' : (Dof x).what₂.LL →+* (Dof x'').what₂.LL) (e' : ↥(Dof x'').LL0 ≃+* ↥(Dof x).LL0), CopyAll (Dof x) (Dof x'') ι' e' ∧
      SameFrame (cfOf x) (cfOf x'') ∧ HEq l.Pq l''.Pq ∧
      ∃ (g : Geo x) (g'' : Geo x'') (hg : GlobalTheory.RealGeo.InGeo g) (hg'' : GlobalTheory.RealGeo.InGeo g'') (a : BigHost (Dof x))
        (a'' : BigHost (Dof x'')), Nonempty (GlobalTheory.TwInputs.Move.RealMove (sideAt x g hg a) (sideAt x'' g'' hg'' a'') ι') := by
  have hD : Dof x'' = N.toD7 := by
    show (w'.st x''.o.Z).toD7 = N.toD7
    rw [ho]; rfl
  obtain ⟨ι', e', h⟩ := copyAll_ex hN hG.pl hD
  obtain ⟨h1, h2, h3, h4⟩ := fr_same hE.1 ((heq_of_eq w'.C_eq).trans (hf.trans (heq_of_eq w.C_eq).symm))
  obtain ⟨g, g'', hg, hg'', hX⟩ := GlobalTheory.HeightCounting.SerMove.exists_geo_extN hExt x x''
  have hO' : K.Over B.toPre := hE.1 ▸ hO
  exact ⟨ι', e', h, ⟨(by with_unfolding_all exact (h1 :)), (by with_unfolding_all exact (h2 :)), (by with_unfolding_all exact (h3 :)), (by with_unfolding_all exact (h4 :))⟩,
    (by with_unfolding_all exact ((choice_heq hE.1 (p := (l.Pq)) (p' := (l''.Pq)) ((l.Pq_over)) ((l''.Pq_over)) (s := (w.I.sel)) (s' := (w'.I.sel)) ((hsel)) ((l.sel)) ((l''.sel))) : _)),
    g, g'', hg, hg'', bigHost_st hO' hB x, bigHost_st hO hB x'',
    GlobalTheory.HeightCounting.SerMove.realMove_of_link x x'' ι' e' g g'' ⟨hO, hKP, hF, hS', hE, hf, hSt, hpx, hsel, hJ, hδ, hExt, h.cp, ⟨h.cp.gal, h.pl⟩, hX⟩ hg hg'' _ _⟩
end GlobalTheory.HeightCounting.SerGlue
end
end
