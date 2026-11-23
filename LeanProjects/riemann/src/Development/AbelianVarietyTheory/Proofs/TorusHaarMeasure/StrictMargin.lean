import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpCStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH

namespace GlobalTheory.InterpC

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem strict_margin (r : ℕ) (X : Data E r) (Xa : ArchInM X) :
    ∃ η : ℝ, 0 < η ∧ ∀ x0, IsOrth X x0 →
      ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        2 * η * leviO X x0 (phla X Xa.L) z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
          (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ +
          leviO X x0 (fun x => (1 + Xa.c1 / Xa.a1) * Xa.ps0 x) z ξ := by
  obtain ⟨η, hη, hF⟩ := Xa.posF
  refine ⟨η, hη, fun x0 ho z hz ξ => ?_⟩
  have ht : 0 < 1 + Xa.c1 / Xa.a1 := by have := Xa.frame_theta_const_pos; have := Xa.frame_theta_weight_pos; positivity
  have hx0 := IW.orth_mem_dom X x0 ho
  have h := hF (1 + Xa.c1 / Xa.a1) ht.le (by rw [mul_comm]; exact Xa.rr_le) x0 hx0 z hz ξ
  rw [IW.leviM_comb X x0 ho hz] at h
  have hca : ContDiffAt ℝ 2 (fun w => Xa.ps0 (cpt X x0 w)) z :=
    ((Xa.potential_smooth x0 hx0).contDiffAt ((ExF.isOpen_OmF X x0).mem_nhds hz)).of_le
      (show (2 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) from WithTop.coe_le_coe.2 le_top)
  rw [IC.leviO_smul X x0 Xa.ps0 _ hca ξ]
  have h2 := mul_le_mul_of_nonneg_left (Xa.base_psi_levi_lower_bound x0 hx0 z hz ξ) ht.le
  simp only [leviO] at h h2 ⊢
  nlinarith [h, h2]

theorem main : PoinStatement (E := E) → KronHolPsiStatement (E := E) → InterpCStatement (E := E) :=
  fun hP hK => interpC_of hP hK strict_margin

end GlobalTheory.InterpC
