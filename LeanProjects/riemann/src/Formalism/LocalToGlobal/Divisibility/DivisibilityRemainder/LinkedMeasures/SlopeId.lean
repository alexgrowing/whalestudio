import Formalism.SharpRestriction.Divisibility.HookProducts.HhOfInputs
import Formalism.LocalToGlobal.Divisibility.RecBridgeWire
import Formalism.LocalToGlobal.ClassOfRecordOfChoice
import Formalism.SharpRestriction.GlobalSchurBounds.LogXLowerFamilyOfTheorems

noncomputable section

namespace Formalism.SlopeId

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory

theorem muZero_free {eps : ℝ} (Fm : FamP eps) : J.MuZero Fm := Formalism.L2.DIV.Wire.za_of Fm

theorem muTu_of_size {eps : ℝ} (Fm : FamP eps) (h : Formalism.MainNotions.TuSize Fm) : J.MuTu Fm := by
  obtain ⟨x0, h⟩ := h
  refine ⟨2 * |Fm.CTu|, x0, fun x hx i u => ?_⟩
  refine ((h x hx i).2 u).trans ?_
  have hb := J.th_bounds (Fm.L x i)
  have hL1 : (Fm.L x i).sc.L ≤ (Fm.L x i).sc.x := by
    unfold Scale.L
    exact J.scale_rpow_le_self_of_le_one _ (by linarith [hb.1, hb.2.1])
  have hL0 : 0 ≤ (Fm.L x i).sc.L := Real.rpow_nonneg (zero_lt_one.trans (Fm.L x i).sc.one_lt_alt).le _
  have hm : ((Fm.D x i).R.m : ℝ) ≤ 2 * (Fm.D x i).R.n := by
    have := (Fm.D x i).R.m_le_f
    unfold Ranks.n
    exact_mod_cast this
  have hm0 : (0 : ℝ) ≤ (Fm.D x i).R.m := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ (Fm.D x i).R.n := Nat.cast_nonneg _
  have hX := J.xn_le_Xpp (Fm.L x i).sc (Fm.D x i).R
  have hmL : ((Fm.D x i).R.m : ℝ) * (Fm.L x i).sc.L ≤ 2 * (Fm.L x i).sc.X'' (Fm.D x i).R.n := by
    calc ((Fm.D x i).R.m : ℝ) * (Fm.L x i).sc.L ≤ (2 * (Fm.D x i).R.n) * (Fm.L x i).sc.x :=
          mul_le_mul hm hL1 hL0 (by positivity)
      _ = 2 * ((Fm.L x i).sc.x * (Fm.D x i).R.n) := by ring
      _ ≤ 2 * (Fm.L x i).sc.X'' (Fm.D x i).R.n := by linarith
  calc Fm.CTu * (Fm.D x i).R.m * (Fm.L x i).sc.L = Fm.CTu * (((Fm.D x i).R.m : ℝ) * (Fm.L x i).sc.L) := by ring
    _ ≤ |Fm.CTu| * (((Fm.D x i).R.m : ℝ) * (Fm.L x i).sc.L) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg hm0 hL0)
    _ ≤ |Fm.CTu| * (2 * (Fm.L x i).sc.X'' (Fm.D x i).R.n) := mul_le_mul_of_nonneg_left hmL (abs_nonneg _)
    _ = 2 * |Fm.CTu| * (Fm.L x i).sc.X'' (Fm.D x i).R.n := by ring

theorem muDGam_of_size {eps : ℝ} (Fm : FamP eps) (h : Formalism.MainNotions.DGamSize Fm) : J.MuDGam Fm := J.muDGam_of_fact Fm h

theorem muFG_of_full {eps : ℝ} (Fm : FamP eps) (h : NuFullF Fm) : J.MuFG Fm := by
  obtain ⟨x0, h⟩ := h
  exact ⟨x0, fun x hx i u => (h x hx i u).1⟩

theorem linkMu_of_sizes {eps : ℝ} (Fm : FamP eps) (hT : Formalism.MainNotions.TuSize Fm) (hG : Formalism.MainNotions.DGamSize Fm) (hF : J.MuFG Fm)
    (hR : J.MuRank Fm) : LinkMu Fm :=
  J.linkMu Fm (muZero_free Fm) hF hR (muTu_of_size Fm hT) (muDGam_of_size Fm hG)

theorem linkMu_of_full {eps : ℝ} (Fm : FamP eps) (hT : Formalism.MainNotions.TuSize Fm) (hG : Formalism.MainNotions.DGamSize Fm) (hNF : NuFullF Fm)
    (hR : J.MuRank Fm) : LinkMu Fm :=
  linkMu_of_sizes Fm hT hG (muFG_of_full Fm hNF) hR

end Formalism.SlopeId

end
