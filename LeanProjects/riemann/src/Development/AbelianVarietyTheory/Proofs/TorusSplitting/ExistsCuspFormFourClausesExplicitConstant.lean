import Mathlib
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.EtArch
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.EtaProductFormValuationBoundStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsProductCuspFormNeZeroArchSupNormBoundsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.EtaForm GlobalTheory.EtaAn

namespace GlobalTheory.EtaAn

theorem wtA_wEt_eq_zero (D : D7) (j i : ℕ) : wtA (wEt D j i) = 0 := by
  funext x
  simp [wtA, wEt, WeightAlgebra.wscalar, Formalism.L2.Pj.ext0]

theorem exists_form_four_clauses (D : D7) (T : Top D) (h : LawsP T) (DF q : ℕ) (R0 P tableLineDegreeTwo : ℝ)
    (hrun : RunOK D.host.E D.R.r DF q R0 D.R.m)
    (hp : ∀ j, InR D j → p16 D.host.E D.R.r q D.R.m 5
      (max 1 (Fintype.card (T.U j T.σ₀).Comp) * 5 ^ (8 * I2.PT.f D.host.E * D.R.r ^ 2)) ≤ min P tableLineDegreeTwo)
    (hP : 0 ≤ P) : ETEx h P (EtArch h (I2.th (E := D.host.E) q R0) tableLineDegreeTwo) := by
  intro j h1 h2
  have hj : InR D j := ⟨h1, h2.le⟩
  have hdat := h.pins.2.2.2 j hj
  have hq : (T.Q.Dw j).q ≤ D.R.m := by
    rw [hdat.2.1]; simp [Ranks.sigW]
  have hr : 2 ≤ D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  obtain ⟨i, J, fJ, cf, xs, f, hi, hcard, hsp, hrule, hcusp, hne, -, hnzd, harch, hsup⟩ :=
    GlobalTheory.T.exists_product_cuspForm_ne_zero_arch_supNorm_bounds D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r
      (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) T.σ₀ (fun σ hσ => h.unf j hj σ hσ) T.good_σ₀
      (h.allTest j hj) hr 5 (by decide) (by norm_num) DF q D.R.m R0 hrun (Or.inr hq)
  have hw := wtA_wEt_eq_zero D j i
  have hn : (wEt D j i).n = 2 * 5 ^ 4 * D.R.r * i := rfl
  have hmemC : f ∈ T.C j (wEt D j i) := by
    change f ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA (wEt D j i)) (wEt D j i).n
    rw [hw, hn]; exact hcusp
  have hmem : f ∈ cutR T.C j (wEt D j i) := by rw [cutR_eq T.C hj]; exact hmemC
  have hpj := hp j hj
  have hi' : (0 : ℝ) < i := by exact_mod_cast hi
  refine ⟨i, hi, ⟨f, hmem⟩, ⟨fun h0 => hne (congrArg Subtype.val h0), ?_⟩, ?_, ?_, ?_⟩
  · intro w' G hFG
    have hGc : (G : T.R j) ∈ T.C j w' := cutR_le T.C j w' G.2
    have hm : f * (G : T.R j) ∈ cutR T.C j (WeightAlgebra.wadd (wEt D j i) w') := by
      rw [cutR_eq T.C hj]; exact h.toLawsCore.mul j hj _ w' _ hmemC _ hGc
    have hval : f * (G : T.R j) = 0 := by
      have e1 : incG deg (cutR T.C j) (wEt D j i) ⟨f, hmem⟩ * incG deg (cutR T.C j) w' G = 0 := hFG
      rw [incG_mul deg (cutR T.C j) (deg_wadd (wEt D j i) w') ⟨f, hmem⟩ G hm] at e1
      have e2 := incG_inj deg (cutR T.C j) _ (e1.trans (map_zero _).symm)
      exact congrArg Subtype.val e2
    exact Subtype.ext (hnzd _ _ _ (dom_wtA w') (cusp_le_sec _ _ _ _ _ hGc) hval)
  · exact GlobalTheory.T.etaProductForm_valuation_bound D T h j h1 h2 i ⟨f, hmem⟩ J D.R.r cf xs hcard hsp hrule
  · intro σ
    have e : (recB h.toLawsCore).supN j _ σ ⟨f, hmem⟩ =
        supC (T.Q.Xo j) T.Q.c (T.U j) (xiR D) (goodOf T.Q.c σ) 0 (2 * 5 ^ 4 * D.R.r * i) f := by
      change cutN T.C T.Ns j (wEt D j i) σ ⟨f, hmem⟩ = _
      unfold cutN
      rw [if_pos hj]
      unfold Core.Ns
      rw [hw, hn]
    have hs0 := (recB h.toLawsCore).supN_nonneg j _ σ ⟨f, hmem⟩
    have hb := hsup (goodOf T.Q.c σ) (xiR D) (goodEmb_goodOf _ σ)
    have hb' : (recB h.toLawsCore).supN j _ σ ⟨f, hmem⟩ ≤ Real.exp (i * P) := by
      rw [e]
      refine le_trans hb (Real.exp_le_exp.mpr ?_)
      exact mul_le_mul_of_nonneg_left (hpj.trans (min_le_left _ _)) hi'.le
    rw [div_le_iff₀ hi', mul_comm]
    rcases hs0.eq_or_lt with h0 | h0
    · rw [← h0, Real.log_zero]; positivity
    · exact (Real.log_le_iff_le_exp h0).mpr hb'
  · intro σ hσ k x hx
    have hb := harch σ hσ k x hx
    have hl : lieFac (T.Q.Dw j) (xiR D) 0 = 1 := by simp [lieFac]
    rw [hw, hn, hl, one_mul]
    refine le_trans hb (Real.exp_le_exp.mpr ?_)
    have := hpj.trans (min_le_right _ _)
    refine mul_le_mul_of_nonpos_left ?_ (by linarith)
    exact sub_le_sub_left this _

end GlobalTheory.EtaAn
