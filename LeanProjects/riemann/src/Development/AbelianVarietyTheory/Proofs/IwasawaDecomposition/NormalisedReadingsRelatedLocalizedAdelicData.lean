import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RepOfHeq

noncomputable section

namespace GlobalTheory.HeightCounting.Fin3

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2
  GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

theorem yRel_of_pin : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P)
    (L : LocAll (lay0 (Dof x))) (m : Moved (oL x L)), m.z = datL x L → m.Coh → ∀ (s : Side0 (oL x L)) (r : ReadPk m s), r.Pin →
      ∀ Y : YT x L s.p0, HEq Y r.Y → YRel L Y := by
  intro K B f T w P x L m hz hC s r hP Y hY
  have hR := CopyRead.repOf_heq x.coh x.r x.pin hC r hP
  obtain ⟨z, intersectionNumber_baseChange, exAt, inGeo, Xg, tr, core, eta, W1, y, tup, t, tA⟩ := m
  dsimp only at hz
  subst hz
  obtain ⟨rY, rZ, rtup, rtupT, rPY, rPW, rjA, rjA0, reMt⟩ := r
  dsimp only at hY
  cases hY
  refine ⟨(by with_unfolding_all exact (hR :)), ?_, ?_⟩
  · intro i y
    have heW := hP.eW
    have hf : HEq t.lf.eW x.m.t.lf.eW := hC.eW.trans x.coh.eW.symm
    have h3 : @Eq (type_of% t.lf.eW) t.lf.eW ((by with_unfolding_all exact (x.m.t.lf.eW :))) :=
      @eq_of_heq (type_of% t.lf.eW) t.lf.eW ((by with_unfolding_all exact (x.m.t.lf.eW :))) ((by with_unfolding_all exact (hf :)))
    exact kc% ((heW i y).trans ((heq_of_eq (congrArg (fun g => g i y) h3)).trans (x.pin.eW i y).symm))
  · intro μ h i y
    have hjMt := hP.jMt
    have hf : HEq t.lf.jMt x.m.t.lf.jMt := hC.jMt.trans x.coh.jMt.symm
    have h3 : @Eq (type_of% t.lf.jMt) t.lf.jMt ((by with_unfolding_all exact (x.m.t.lf.jMt :))) :=
      @eq_of_heq (type_of% t.lf.jMt) t.lf.jMt ((by with_unfolding_all exact (x.m.t.lf.jMt :))) ((by with_unfolding_all exact (hf :)))
    exact (by with_unfolding_all exact (((hjMt μ h i y).trans ((heq_of_eq (congrArg (fun g => g μ i y) h3)).trans (x.pin.jMt μ h i y).symm)) :))

end GlobalTheory.HeightCounting.Fin3

end
