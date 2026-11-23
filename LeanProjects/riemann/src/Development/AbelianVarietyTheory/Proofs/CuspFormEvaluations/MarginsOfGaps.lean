import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CurvAndMarginClosed
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameThetaConstPos

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Shares

theorem margins_of_gaps : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X), 0 < X.p0 → X.p0 < r → Nonempty X.Ψ → Xa.de = de2W X → IsStrictDom X Xa.L → (∀ τ (a b : Fin r), a ≤ b → ((b : ℕ) < X.p0 ∨ X.p0 ≤ (a : ℕ)) → (Xa.Fp - kapW X - nd X • Xa.L) τ b ≤ (Xa.Fp - kapW X - nd X • Xa.L) τ a) → ∀ bb m mL : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb → (∀ τ (a b : Fin r), (a : ℕ) < X.p0 → X.p0 ≤ (b : ℕ) → m ≤ (((Xa.Fp - kapW X - nd X • Xa.L) τ b : ℤ) : ℝ) - (((Xa.Fp - kapW X - nd X • Xa.L) τ a : ℤ) : ℝ) ∧ mL ≤ ((Xa.L τ b : ℤ) : ℝ) - ((Xa.L τ a : ℤ) : ℝ)) → bb + 2 * Xa.T < m → bb ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) + bb < m + nd X * mL → 2 * (r : ℝ) < m → Margins X Xa := by
  intro E _ _ _ r X Xa h0 hr _ hde hL hgap bb m mL hbb hpair hm1 hm2 _
  obtain ⟨g1, g2, g3, g4⟩ := GlobalTheory.ThetaRecordCompare.arch_gaps Xa h0 hr
  have hT : (0 : ℝ) ≤ Xa.T := Nat.cast_nonneg _
  have hde2 : GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.IsTwoDelta X Xa.de := by
    rw [hde]
    intro τ i j
    refine ⟨fun h => ?_, fun a b => ?_⟩
    · simp only [de2W]
      split_ifs <;> omega
    · simp only [de2W]
      split_ifs <;> omega
  have hA : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
        (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ := fun x0 ho z hz ξ => by
    rw [← IW.leviM_comb X x0 ho hz]
    exact (GlobalTheory.CurvMarginClosed.curv_and_margin_closed (E := E)).2 r X _ m
      (fun τ i j a b => hgap τ i j a (Or.inl b)) (fun τ i j a b => hgap τ i j b (Or.inr a))
      (fun τ i j a b => (hpair τ i j a b).1) x0 ho z hz ξ
  have hB : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      mL * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.L) z ξ :=
    (GlobalTheory.CurvMarginClosed.curv_and_margin_closed (E := E)).2 r X _ mL
      (fun τ i j a b => by
        rcases a.eq_or_lt with h | h
        · rw [h]
        · exact ((hL τ).1 i j h b).le)
      (fun τ i j a b => by
        rcases b.eq_or_lt with h | h
        · rw [h]
        · exact ((hL τ).2.1 i j a h).le)
      (fun τ i j a b => (hpair τ i j a b).2)
  refine ⟨⟨bb, m - 2 * Xa.T, hbb, by linarith, fun t ht x0 ho z hz ξ => ?_⟩,
    ⟨bb, m + nd X * mL, hbb, hm2, fun x0 ho z hz ξ => ?_⟩, fun x0 ho z hz ξ => ?_,
    (GlobalTheory.ThetaRecordCompare.arch_extra Xa).2.2.2.1,
    fun k P => GlobalTheory.ThetaRecordCompare.cusp_of_gaps Xa.n_ge h0 hr
      (GlobalTheory.ThetaRecordCompare.gaps_add g3 (GlobalTheory.ThetaRecordCompare.gapsGe_mono g1 zero_le_one) k)
      (GlobalTheory.ThetaRecordCompare.pair_add g4 g2 k)⟩
  · have a := hA x0 ho z hz ξ
    have hrh := GlobalTheory.ThetaRecordCompare.leviRh_nonneg X ho hz ξ
    rcases ht with rfl | ht
    · have := mul_nonneg hT hrh
      nlinarith
    · rw [Set.mem_singleton_iff] at ht
      subst ht
      have b := Xa.base_psi_levi_lower_bound x0 (IW.orth_mem_dom X x0 ho) z hz ξ
      have c : leviM X (phla X Xa.de) x0 z ξ = 2 * leviRh X x0 z ξ :=
        GlobalTheory.ThetaRecordCompare.levi_twoDelta hde2 ho hz ξ
      have ht : 0 ≤ 1 + Xa.c1 / Xa.a1 := by have := Xa.frame_theta_const_pos; have := Xa.frame_theta_weight_pos; positivity
      have d := mul_le_mul_of_nonneg_left b ht
      have e := mul_le_mul_of_nonneg_right Xa.rr_le hrh
      rw [c] at d
      unfold leviO at *
      nlinarith
  · have a := hA x0 ho z hz ξ
    have b := mul_le_mul_of_nonneg_left (hB x0 ho z hz ξ) (Nat.cast_nonneg (α := ℝ) (nd X))
    nlinarith
  · by_cases hξ : ξ = 0
    · subst hξ; simp [leviO, leviM, leviV]
    · exact (Xa.posL x0 (IW.orth_mem_dom X x0 ho) z hz ξ hξ).le

end GlobalTheory.Shares
