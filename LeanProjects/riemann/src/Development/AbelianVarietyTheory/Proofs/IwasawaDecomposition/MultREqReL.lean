import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RelabelledWeight

noncomputable section

namespace GlobalTheory.Mem.SRe

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV
  Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.MainNotions Formalism.L2.Forms NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Top.Bl

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000 in

theorem multR_eq_reL {B : Base} {C : Cols B} (a : Late B C) (Z : New a.D) {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type}
    {A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]
    (R : RealDat a.D A Ks) (F : Face a.D A) :
    MultR R F = (by with_unfolding_all exact ((letI := alg (reL a Z) iK; MultR (real (reL a Z) R) (face (reL a Z) F)) :)) := (congrArg (fun m ↦ m R.θ (R.MY 0) (JR R F) (chiR R F)) (mult_eq (reL a Z) a))

set_option maxHeartbeats 4000000 in

theorem mvSee : MvSee := by
  intro B C a Z G' _ _ Pl0 T A Ks _ _ iK R F X h t hs
  obtain ⟨h1, h2, σ, red, hA, ⟨hr, hB⟩, hC⟩ := hs
  have hB' := cast (congrArg (fun E : Submodule ℂ (MMap (MP R)) => ∀ k ∈ X.B.I.Kset, ∀ T ∈ E, ∀ (v : (MP R).Vec)
    (g : GA a.D (Yc a.D 0)), (T : MMap (MP R)) v (g * kap X h t k) =
      actL (Yc a.D 0) (R.βY 0) (R.dat0 R.triv) (R.eG (σ (red k))) ((T : MMap (MP R)) v) g) (multR_eq_reL a Z R F)) hB
  letI := alg (reL a Z) iK
  refine ⟨?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact (h1 :))
  · kexactB h2
  · refine ⟨(by with_unfolding_all exact (σ :)), (by with_unfolding_all exact (red :)), ?_, ⟨?_, ?_⟩, ?_⟩
    · exact (by with_unfolding_all exact (hA :))
    · exact (by with_unfolding_all exact (hr :))
    · kexactB hB'
    · exact (by with_unfolding_all exact (hC :))

end GlobalTheory.Mem.SRe

end
