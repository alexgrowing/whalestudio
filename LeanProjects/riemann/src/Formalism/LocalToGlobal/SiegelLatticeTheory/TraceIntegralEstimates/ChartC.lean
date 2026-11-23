import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.StCoordVCoef
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.ChartLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RootPatterns
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ChartC
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FormTransp
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan

noncomputable section

open scoped Matrix Classical
open MeasureTheory Finset NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.L2.SG.LocWSOf

namespace Formalism.L2.S.Pv.Chart

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ) (u u' : D.what₂.Word)
  (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf) (τ : D.what₂.Tau)

include C

theorem place_chart (hrep : IsPtRep X u u' w γ) :
    ∃ ψ : (rootPat (ptLoc D τ w) → ℂ) → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS,
      (∀ y, Matrix.of (ψ y) ∈ Formalism.MainNotions.S.Rset D.R.k D.R.rS (Formalism.L2.SG.RealFrameCoordinates.g0 C γ τ) ∧
        rootCoords D.R.k D.R.rS (zB X (C.Qi τ) u' τ) (ptLoc D τ w) (ψ y) = y) ∧
      ∀ x, Matrix.of x ∈ Formalism.MainNotions.S.Rset D.R.k D.R.rS (Formalism.L2.SG.RealFrameCoordinates.g0 C γ τ) →
        ψ (rootCoords D.R.k D.R.rS (zB X (C.Qi τ) u' τ) (ptLoc D τ w) x) = x := by
  obtain ⟨hzW, hTz⟩ := Formalism.L2.SG.Pf.zTr C u τ
  obtain ⟨hzW', hTz'⟩ := Formalism.L2.SG.Pf.zTr C u' τ
  have hT : ∀ u0 : D.what₂.Word, 0 < Tr D u0 := fun u0 => by
    unfold Tr
    exact Nat.cast_pos.2 (D.mem u0).A.T_prime.pos
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hg0 : Formalism.L2.SG.RealFrameCoordinates.g0 C γ τ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) :=
    Formalism.L2.SG.Pf.LTL.trG_mem _ _ _ (C.isT τ).2.1 (C.isT τ).2.2.1 _
  exact locChart D.R.k D.R.rS hk _ _ hzW (by rw [hTz]; exact hT u) hzW' (by rw [hTz']; exact hT u') (ptLoc D τ w) _
    hg0 (Formalism.L2.SG.RealFrameCoordinates.zhat_conjugator_eq_point C u u' w γ hrep τ)

theorem stCoordV_inj (hrep : IsPtRep X u u' w γ) {y₁ y₂ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))}
    (h₁ : y₁ ∈ Formalism.L2.SG.NGPin.StV X u u' γ (vOf X τ)) (h₂ : y₂ ∈ Formalism.L2.SG.NGPin.StV X u u' γ (vOf X τ))
    (h : Formalism.L2.SG.NGPin.stCoordV X u' w γ (vOf X τ) y₁ = Formalism.L2.SG.NGPin.stCoordV X u' w γ (vOf X τ) y₂) :
    y₁ = y₂ := by
  obtain ⟨ψ, -, hψ⟩ := place_chart C u u' w γ τ hrep
  rw [Formalism.L2.SG.RootPatterns.stCoordV_comp C u' w γ τ] at h
  have h' := (MeasurableEquiv.piCongrLeft (fun _ : FreeE w => ℂ) (Formalism.L2.SG.RootPatterns.idxF τ w)).injective h
  have m₁ := (Formalism.L2.SG.RealConjugatorData.stV_iff C γ τ u u' y₁).1 h₁
  have m₂ := (Formalism.L2.SG.RealConjugatorData.stV_iff C γ τ u u' y₂).1 h₂
  have e := congrArg ψ h'
  simp only [Function.comp_apply] at e
  rw [hψ (Formalism.L2.SG.RealConjugatorData.cMr C γ τ y₁) m₁, hψ (Formalism.L2.SG.RealConjugatorData.cMr C γ τ y₂) m₂] at e
  exact (Formalism.L2.SG.RealConjugatorData.cMr_closedEmb C γ τ).injective e

theorem stCoordV_surj (hrep : IsPtRep X u u' w γ) (x : FreeE w → ℂ) :
    ∃ y ∈ Formalism.L2.SG.NGPin.StV X u u' γ (vOf X τ), Formalism.L2.SG.NGPin.stCoordV X u' w γ (vOf X τ) y = x := by
  obtain ⟨ψ, hψ, -⟩ := place_chart C u u' w γ τ hrep
  set e := MeasurableEquiv.piCongrLeft (fun _ : FreeE w => ℂ) (Formalism.L2.SG.RootPatterns.idxF τ w)
  obtain ⟨hm, hc⟩ := hψ (e.symm x)
  obtain ⟨y, hy⟩ := Formalism.L2.SG.RealConjugatorData.rset_range C γ τ _ hm
  refine ⟨y, (Formalism.L2.SG.RealConjugatorData.stV_iff C γ τ u u' y).2 (by rw [hy]; exact hm), ?_⟩
  rw [Formalism.L2.SG.RootPatterns.stCoordV_comp C u' w γ τ]
  simp only [Function.comp_apply]
  rw [hy, hc, e.apply_symm_apply]

theorem stCoordV_meas : Measurable (Formalism.L2.SG.NGPin.stCoordV X u' w γ (vOf X τ)) := by
  rw [Formalism.L2.SG.RootPatterns.stCoordV_comp C u' w γ τ]
  exact (MeasurableEquiv.measurable _).comp ((Formalism.L2.SG.RootPatterns.rootCoords_cont _ _ _ _).measurable.comp
    (Formalism.L2.SG.RealConjugatorData.cMr_measEmb C γ τ).measurable)

end Formalism.L2.S.Pv.Chart

end
