import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable

open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

namespace GlobalTheory.LvT

theorem PtModel.mem_Fi_iff_exists_isExt : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i)
    (φ : Fn X i), φ ∈ X.fm.Fi i ↔ ∃ Φ, M.IsExt φ Φ := by
  intro D u X i M φ
  rw [M.mem_Fi]
  constructor
  · intro h
    choose y hy hfix using h
    choose cl gp hp using M.rep_surj
    have key : ∀ (c c' : X.C.cls i) (g g' : M.G), g • M.rep c = g' • M.rep c' →
        M.act g (y c) = M.act g' (y c') := by
      intro c c' g g' hgg
      have h1 : (g'⁻¹ * g) • M.rep c = M.rep c' := by
        rw [mul_smul, hgg, inv_smul_smul]
      have hc := M.rep_inj c c' _ h1
      subst hc
      have h2 := hfix c _ h1
      have h3 : g = g' * (g'⁻¹ * g) := by group
      conv_lhs => rw [h3, map_mul, Module.End.mul_apply, h2]
    refine ⟨fun p => M.act (gp p) (y (cl p)), fun c => ?_, fun g p => ?_⟩
    · have := key (cl (M.rep c)) c (gp (M.rep c)) 1 (by rw [hp, one_smul])
      rw [hy c]
      simp only [this, map_one, Module.End.one_apply]
    · have := key (cl (g • p)) (cl p) (gp (g • p)) (g * gp p) (by rw [hp, mul_smul, hp])
      simp only [this, map_mul, Module.End.mul_apply]
  · rintro ⟨Φ, h1, h2⟩ c
    refine ⟨Φ (M.rep c), h1 c, fun g hg => ?_⟩
    rw [← h2, hg]

end GlobalTheory.LvT
