import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OfRoots

noncomputable section

open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S
open scoped Classical

namespace GlobalTheory.LoopVol

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem root_fst_lt (w : Point D.host.E (D.R.rS + 1)) (q : GlobalTheory.LoopV.roots (ptMat w)) : q.1.1.1 < D.R.rS := by
  have hq := q.2
  simp only [GlobalTheory.LoopV.roots, Finset.mem_filter] at hq
  have h := hq.2.1
  have h2 := q.1.2.2
  rw [Fin.lt_def] at h
  omega

def ratCoord (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
    (γ s y : X.B.I.Ginf) : D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ :=
  fun τ q => Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε (X.pl.symm τ))
    (Formalism.L2.SG.HidaSetting.rv X.B.I (X.pl.symm τ) (X.fR ⟨q.1.1.1, root_fst_lt w q⟩))
    (uMat ((γ⁻¹ * (s⁻¹ * y * s) * γ) (X.pl.symm τ)) *ᵥ Formalism.L2.SG.RealObj.frm X u' 1 (X.pl.symm τ) q.1.2)

theorem ratCoord_cont (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
    (γ s : X.B.I.Ginf) : Continuous (ratCoord X u' w γ s) := by
  unfold ratCoord Formalism.L2.SG.HidaSetting.hJ
  refine continuous_pi fun τ => continuous_pi fun q => ?_
  refine Continuous.dotProduct continuous_const (Continuous.matrix_mulVec continuous_const ?_)
  refine Continuous.matrix_mulVec ?_ continuous_const
  exact Units.continuous_val.comp (continuous_subtype_val.comp ((continuous_apply _).comp
    ((continuous_const.mul ((continuous_const.mul continuous_id).mul continuous_const)).mul continuous_const)))

end GlobalTheory.LoopVol

end
