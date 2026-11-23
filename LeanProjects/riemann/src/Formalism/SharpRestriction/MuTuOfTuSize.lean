import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.AdmissibleParameterJoins
import Formalism.SharpRestriction.AdmissibleParameterJoins.SumLogPrimeFactorsLe
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
import Formalism.SizeWindowBrackets.ChainSlopeWindows.PChain

noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions

def AllLinks {eps : ℝ} (Fm : FamP eps) (CV Cabs CH C0 eD eL : ℝ) : Prop :=
  LinkV Fm CV ∧ LinkShaFin Fm ∧ LinkN Fm ∧ LinkEta Fm ∧ LinkIRR Fm ∧ SmallLevelRankEq Fm ∧ LinkDIVt Fm Cabs CH ∧
    ((NuFullF Fm ∧ J.MuRank Fm) ∧ J.MuTu Fm ∧ J.MuDGam Fm) ∧
    LinkG Fm ∧ LinkS Fm C0 ∧ LinkGLOBAL Fm Cabs CH C0 eD eL

abbrev WithTw (𝒞 : FamClass) : FamClass := fun Fm => 𝒞 Fm ∧ TwGood Fm

theorem Closed.withTw {𝒞 : FamClass} {P : ∀ {eps : ℝ}, FamP eps → ℝ → Prop} (h : Closed 𝒞 P) :
    Closed (WithTw 𝒞) P := by
  obtain ⟨a, ha, h⟩ := h
  refine ⟨a, ha, fun e he hle => ?_⟩
  obtain ⟨K, hK⟩ := h e he hle
  exact ⟨K, fun Fm CH hc hL => hK Fm CH hc.1 hL⟩

theorem muTu_of_tuSize {eps : ℝ} (Fm : FamP eps) (h0 : 0 < eps) (h : TuSize Fm) : J.MuTu Fm := by
  obtain ⟨x0, h⟩ := h
  have ht : Filter.Tendsto (fun x : ℝ => x ^ (eps / 100)) Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop (by positivity)
  obtain ⟨x2, hx2⟩ := Filter.eventually_atTop.1 (ht.eventually_ge_atTop Fm.CTu)
  refine J.muTu_of_sizeTu Fm ⟨max (max x0 x2) (Fm.x1 + 1), fun x hx i u => ?_⟩
  have a0 : x ≥ x0 := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have a2 : x ≥ x2 := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have a1 : Fm.x1 < x := lt_of_lt_of_le (by linarith) ((le_max_right _ _).trans hx)
  refine ((h x a0 i).2 u).trans ?_
  have hL : 0 ≤ (Fm.L x i).sc.L := Real.rpow_nonneg (zero_lt_one.trans (Fm.L x i).sc.one_lt_alt).le _
  have hC : Fm.CTu ≤ (Fm.L x i).sc.x ^ szTh (Fm.L x i) := by
    unfold szTh; rw [Fm.L_x x i a1, Fm.L_eps x i]; exact hx2 x a2
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg _)) hL

end Formalism.MainNotions

end
