import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.ClassFrameOO3FrameValTrans
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepPtRepPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SpanPreservation
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.HermitianCombinationZ

noncomputable section

open Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.RowForm

namespace LocalFrameDecomposition

variable {D : Formalism.BasicNotions.D7} (X : HidaSetting D)

theorem frameLoc (w : D.what₂.Word) (v : NumberField.InfinitePlace X.B.I.F) :
    PI.SchurPlaces.LeviLA.Frame (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a))
      (rv X.B.I v (X.zR w)) (X.wfr w v) where
  ee := (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X w v).ee
  ef := (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X w v).ef
  ff := (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X w v).ff
  ez := (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X w v).ez
  fz := (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X w v).fz
  ew := (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X w v).ew
  fw := (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X w v).fw
  zw := (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X w v).zw
  ww := (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X w v).ww
  zz := fun h0 =>
    (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X w v).T_ne
      (neg_eq_zero.1 (((Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X w v).zz).symm.trans h0))
  card := by
    have h := (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X w v).card
    omega

end LocalFrameDecomposition

variable {D : Formalism.BasicNotions.D7} (X : HidaSetting D)

theorem sDecompC_holds (w : D.what₂.Word) : SDecompC X w := by
  intro g hg
  have hgi : g⁻¹ ∈ X.SinfU w := Formalism.L2.SG.RealObj.InfCut.sinfU_inv X w hg
  have hS : ∀ v, InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR w)) (uMat (g⁻¹ v)) := hgi
  choose V hVu hVe hVf hVz _ hVN using fun v =>
    PI.SchurPlaces.LeviLA.levi_place (LocalFrameDecomposition.frameLoc X w v)
      ((g⁻¹ v : Formalism.REAL.UJ (X.B.I.ε v)) : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) (g⁻¹ v).2 (hS v)
  let s0 : X.B.I.Ginf := fun v => ⟨V v, hVu v⟩
  have hs0 : ∀ v, uMat (s0 v) = (V v : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) := fun v => rfl
  have hs0H : s0 ∈ HsetU X w := by
    intro v p hp
    rw [hs0]
    rcases hp with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hp
    · exact hVe v a
    · exact hVf v a
    · rw [Set.mem_singleton_iff] at hp
      subst hp
      exact hVz v
  have hN : s0⁻¹ * g⁻¹ ∈ X.NinfU w := fun v => by
    have e : uMat ((s0⁻¹ * g⁻¹) v) =
        (((V v)⁻¹ : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) *
          uMat (g⁻¹ v) := rfl
    rw [e]
    exact hVN v
  have hN' := Formalism.L2.SG.RealObj.SpanPreservation.ninfU_inv X w hN
  rw [_root_.mul_inv_rev, inv_inv, inv_inv] at hN'
  exact ⟨g * s0, hN', s0⁻¹, Formalism.L2.SG.RealObj.InfCut.hsetU_inv X w hs0H, by group⟩

end Formalism.L2.SG.Pf.RowForm
