import Formalism.HermitianCurvature.HermitianCurvatureProofs.CccoefMono
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn

open Filter Topology

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt

theorem limit_of_module_forms : Formalism.FourierDecayAlt.KB.FormLimit := by
  intro Cb
  obtain ⟨Cl, _, hL⟩ := PBE.belowTop
  obtain ⟨Ct, hT⟩ := PBE.formLimit_top Cb
  refine ⟨max Cl Ct, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P0 p f χ ε A N cut hDD hχ hε hf hfA hA hcut
  refine ⟨fun n => PBE.cutCpt P0 p.T.base f χ ε cut hχ hε hf hcut n, ?_⟩
  intro i w hwc hw a b
  have hX : 0 ≤ ((P0.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P0.r : ℝ) + P0.k + 1) ^ 2 + (2 * (P0.r : ℝ) + P0.k + 1) ^ 3) := by
    positivity
  rcases lt_trichotomy i (P0.r + 1) with hlt | heq | hgt
  · exact hL (max Cl Ct) (le_max_left _ _) Wp Wq P0 p f χ ε A N cut hχ hε hf hfA hA hcut i (by omega) w hw a b
  · subst heq
    refine hT Wp Wq P0 p f χ ε A N cut hDD hχ hε hf hfA ?_ hcut w hwc hw a b
    refine le_trans ?_ hA
    have := mul_le_mul_of_nonneg_right (le_max_right Cl Ct) hX
    nlinarith
  · have h0 : ∀ F, p.RR F i w a b = 0 := by
      intro F
      unfold KB.Pl.RR D.RRplace
      split_ifs <;> first | rfl | (exfalso; omega)
    simp only [h0]
    exact tendsto_const_nhds

end Formalism.FourierDecayAlt.P
