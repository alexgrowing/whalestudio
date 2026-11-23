import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPageRunRecord

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldSize

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2
open Formalism.MainNotions.Gaps.EtaleWeightGaps.Num
open scoped IntermediateField

theorem scale_le_rank {D : D7} {L : SizeData₂ D} (S : SizesAt L) : L.sc.x ≤ (D.R.r : ℝ) := by
  have hx1 := L.sc.one_lt_alt.le
  have he := L.sc.eps_pos
  have h1 : L.sc.x ≤ L.sc.x ^ (9 / 2 + 10 * L.sc.eps - szTh L) := by
    calc L.sc.x = L.sc.x ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by unfold szTh; linarith)
  exact (h1.trans S.2.2.1.1).trans (Pm.k_le_r D)

theorem hostSz_of_sizes : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (_Tp : ParamsT D L Pm), SizesAt L →
    (∀ i, Real.log (D.host.g i) ≤ 9 * L.sc.L + 1) → (10 : ℝ) ^ 60 ≤ L.sc.x →
    HostSz D.host L.sc.L ∧ (Sz (FO D) (poR D.R L.sc.L) (poR D.R L.sc.L) → FieldSmall D L) := by
  intro D L P _ S hg hx
  have hL := Pm.one_le_L L
  have h6 := Pm.six_le_r D
  have hf := Pm.two_le_f D
  refine ⟨⟨?_, ?_, ?_, hg, P.pde_log, ?_⟩, fun h => h.2⟩
  · have h : ((62 : ℕ) : ℝ) ≤ D.R.r := le_trans (by norm_num) (hx.trans (scale_le_rank S))
    exact_mod_cast h
  · have h1 := Pm.log_r_le P
    have h2 : Real.log 2 ≤ Real.log (D.R.r : ℝ) := Real.log_le_log (by norm_num) (by linarith)
    linarith [Real.log_two_gt_d9]
  · linarith [Pm.log_f_le P]
  · have h : Real.log |((discr D.host.E : ℤ) : ℝ)| ≤ 2 * D.R.f * L.sc.L := logdE_le_two_f_L P
    rw [div_le_iff₀ (by linarith)]
    nlinarith

end GlobalTheory.FieldSize
