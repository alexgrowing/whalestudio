import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReadPk
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinTypRepCast
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw

theorem hd_tr : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m) (R : RealDat a.D A Ks) (y : Hd R), ∃ y' : HdB b R, Same b y y' := by
  intro B C a b G _ _ Pl0 T Ks _ _ iK A R y
  letI := alg b iK
  let y' : HdB b R :=
    { tup := (by with_unfolding_all exact (y.tup :))
      tupT := (by with_unfolding_all exact (y.tupT :))
      tupT_tup := (by with_unfolding_all exact (y.tupT_tup :))
      tup0 := (by with_unfolding_all exact (y.tup0 :))
      hm := (by with_unfolding_all exact (y.hm :))
      hTop := topMult_tr b y.hTop
      hinj := inj_tr b y.hinj
      PY := (by with_unfolding_all exact ((rowPsi b y.PY) :))
      PW := fun i => (by with_unfolding_all exact ((rowPsi b (y.PW i)) :))
      ιW := (by with_unfolding_all exact (y.ιW :))
      isomFin := fun i => ⟨(by with_unfolding_all exact ((y.isomFin i).bij :)), (by with_unfolding_all exact ((y.isomFin i).conj :)), (by with_unfolding_all exact ((y.isomFin i).lat :))⟩
      frameMatch := (by with_unfolding_all exact (y.frameMatch :))
      hF := (by with_unfolding_all exact (y.hF :))
      stdPsi := (by with_unfolding_all exact (y.stdPsi :)) }
  exact ⟨y', ⟨(by with_unfolding_all exact ((HEq.refl y.tup) :)), (by with_unfolding_all exact ((HEq.refl y.tupT) :)), (by with_unfolding_all exact ((HEq.refl y.PY.ψ) :)), (by with_unfolding_all exact ((HEq.refl fun i => (y.PW i).ψ) :))⟩⟩

end GlobalTheory.Mem.R3.Rw

end
