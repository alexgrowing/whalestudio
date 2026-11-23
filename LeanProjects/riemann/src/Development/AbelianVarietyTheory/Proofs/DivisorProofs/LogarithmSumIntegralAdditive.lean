import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TangentEqLcZero

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open MvPowerSeries ReciprocityTheory.PGsh GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.LawLog

theorem exp_point_zero {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ} (G : LogFGL v d)
    (σ : Type) : expPt G (0 : Fin d → MvPowerSeries σ C) = 0 := by
  funext i
  have h0 : ∀ j, constantCoeff ((0 : Fin d → MvPowerSeries σ C) j) = 0 := fun _ => by simp
  have hs : HasSubst (0 : Fin d → MvPowerSeries σ C) := hasSubst_of_constantCoeff_zero h0
  ext e
  simp only [expPt, Pi.zero_apply]
  rw [coeff_subst hs, map_zero]
  apply finsum_eq_zero_of_forall_eq_zero
  intro m
  by_cases hm : m = 0
  · subst hm
    simp [coeff_zero_eq_constantCoeff_apply, (isExp_expOf G).1 i]
  · obtain ⟨s, hsm⟩ : ∃ s, m s ≠ 0 := by
      by_contra hc; push_neg at hc; exact hm (Finsupp.ext hc)
    have : (m.prod fun s n => ((0 : Fin d → MvPowerSeries σ C) s) ^ n) = 0 := by
      rw [Finsupp.prod]
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hsm)
      simp [zero_pow hsm]
    rw [this, map_zero, smul_zero]

theorem log_sum_additive_preserves_integrality : AddSt := by
  intro C _ v d G σ _
  have hadd : ∀ w w' : Fin d → MvPowerSeries σ C, (∀ i, constantCoeff (w i) = 0) →
      (∀ i, constantCoeff (w' i) = 0) →
      expPt G (w + w') = fun i => subst (Sum.elim (expPt G w) (expPt G w')) (G.F i) := by
    intro w w' hw hw'
    set a : Fin d ⊕ Fin d → MvPowerSeries σ C := Sum.elim (expPt G w) (expPt G w') with ha_def
    have ha0 : ∀ s, constantCoeff (a s) = 0 := by
      rintro (b | b)
      · exact cc_expPt G hw b
      · exact cc_expPt G hw' b
    have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0
    have hF : HasSubst G.F := hasSubst_of_constantCoeff_zero G.F_const
    set y : Fin d → MvPowerSeries σ C := fun i => subst a (G.F i) with hy_def
    have hy0 : ∀ i, constantCoeff (y i) = 0 := fun i =>
      constantCoeff_subst_eq_zero ha ha0 (G.F_const i)
    have hlg : lgPt G y = w + w' := by
      funext i
      have h1 := subst_comp_subst_apply hF ha (G.lg i)
      have hXl : HasSubst (fun b : Fin d => (X (Sum.inl b) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
        hasSubst_of_constantCoeff_zero (fun b => by simp)
      have hXr : HasSubst (fun b : Fin d => (X (Sum.inr b) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
        hasSubst_of_constantCoeff_zero (fun b => by simp)
      rw [G.lg_F, subst_add ha, subst_comp_subst_apply hXl ha, subst_comp_subst_apply hXr ha] at h1
      have hl : (fun s : Fin d => subst a (X (Sum.inl s) : MvPowerSeries (Fin d ⊕ Fin d) C)) = expPt G w := by
        funext s; rw [subst_X ha]; rfl
      have hr : (fun s : Fin d => subst a (X (Sum.inr s) : MvPowerSeries (Fin d ⊕ Fin d) C)) = expPt G w' := by
        funext s; rw [subst_X ha]; rfl
      rw [hl, hr] at h1
      have e1 : subst (expPt G w) (G.lg i) = w i := by
        have := congrFun (lgPt_expPt G hw) i; exact this
      have e2 : subst (expPt G w') (G.lg i) = w' i := by
        have := congrFun (lgPt_expPt G hw') i; exact this
      show subst y (G.lg i) = w i + w' i
      rw [hy_def, ← h1, e1, e2]
    rw [← hlg, expPt_lgPt G hy0]
  refine ⟨⟨fun i => by simp, fun i => ?_⟩, hadd, ?_⟩
  · rw [exp_point_zero G σ]; intro α; simp [IsIntV]
  · intro w w' hw hw'
    refine ⟨fun i => by simp [hw.1 i, hw'.1 i], fun i => ?_⟩
    rw [hadd w w' hw.1 hw'.1]
    refine ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v (G.F_int i) ?_ ?_
    · rintro (b | b)
      · exact hw.2 b
      · exact hw'.2 b
    · rintro (b | b)
      · exact cc_expPt G hw.1 b
      · exact cc_expPt G hw'.1 b

end GlobalTheory.IsoTriv
