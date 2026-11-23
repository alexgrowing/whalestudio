import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BudgetAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientWeightGapBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightConditionsAtIndexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineC1LogBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasUnramifiedIntegralFramedPointsOfGoodPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeySectionInverseRootTwistingSectionSpreadStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwSecOfConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulInvPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspOnRestrict
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.ThinTwist

open GlobalTheory.FlatTw GlobalTheory.FlatLine in

private theorem exists_twist_const (hP : Hypotheses2) {D : D7} (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ)
    (hT : LawsJ T) (hj : InR D j) (hY : Y.Good e o) (hF : FlatExists Y.U (xiR D))
    (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (w₀ : Psi T.Q.H → ℤ) (m : ℕ) (Z : Comp Y.d.Xo₂ Y.d.c₂)
    (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) {f : Rul Y.d.Xo₂ Y.d.c₂}
    (hf : f ∈ cuspW Y.d.Xo₂ Y.d.c₂ Y.U (wtOf (T.Q.Dw j) (u + parWt (T.Q.Dw j) w₀) m)) :
    ∃ g ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0), ∃ K : ℝ, 0 < K ∧
      ∀ z ∈ framesOn (Y.U σ) Z, ptN (modelWt (Y.U σ) (wtOf (T.Q.Dw j) u 0)) (rdU (Y.U σ) g) z =
        K * ptN (modelWt (Y.U σ) (wtOf (T.Q.Dw j) (u + parWt (T.Q.Dw j) w₀) m)) (rdU (Y.U σ) f) z := by
  have hL := GlobalTheory.T.complexUniformizationLaws_of_goodDeepCover D T j Y e o hT hj hY
  have hN := GlobalTheory.T.hasUnramifiedIntegralFramedPoints_of_goodPlaces hP.q18 hP.q1 hP.p5 _ _ _ Y.d.l₂ Y.d.Xo₂ Y.d.c₂ hL.pos
  obtain ⟨hK, ht⟩ := GlobalTheory.T.exists_keySection_inverseRoot_twistingSection_spread _ _ _ _ _ _ _ Y.U hL.unf (xiR D) hL.xi hL.geo hL.pos hL.good hN
  obtain ⟨t, ht1, ht2⟩ := ht Z
  obtain ⟨s, -, -, -, hs1, hs2⟩ := (GlobalTheory.FlatTwisting.twSec_of_flat _ _ _ _ _ _ _ Y.U (xiR D) _ hK hL.unf hL.pos hN).1 Z (-w₀) _
      (FlatSec.shift (hasPts Y.U hL.pos hL.good hL.unf Z) (fun τ => (hF.nonempty Z τ).some) (-w₀))
      ((Set.finite_iUnion fun τ => finite_flDefect_vw (Dw := T.Q.Dw j) (c := Y.d.c₂) τ).subset fun w hw => by
        by_contra hn
        simp only [Set.mem_iUnion, Function.mem_support, not_exists, not_not] at hn
        exact hw (by simp [Finset.sum_apply, hn]))
  obtain ⟨tw, -, -⟩ := GlobalTheory.CombTw.exists_twSec_comb _ _ _ _ _ _ _ Y.U hL.unf (xiR D) _ Z u w₀ m _ s t hs1 hs2 ht1 ht2
  set G := wtOf (T.Q.Dw j) (u + parWt (T.Q.Dw j) w₀) m with hGdef
  have hB : Even G.2 := GlobalTheory.AllWt.even_wtOf _ _
  have hGG : G + (wtOf (T.Q.Dw j) u 0 - G) = wtOf (T.Q.Dw j) u 0 := add_sub_cancel _ _
  have hfZ : idem Z * f ∈ cuspOn Y.U Z G :=
    ⟨GlobalTheory.CompRestr.idem_mul_mem_cuspW hL.unf Z hf, by rw [mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)⟩
  have hmem : f * tw.sig ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0) := by
    have h := tw.cusp_sig G hB _ hfZ
    rwa [hGG, mul_comm (idem Z) f, mul_assoc, tw.idem_sig] at h
  have key : ∀ z ∈ framesOn (Y.U (goodOf Y.d.c₂ σ)) Z,
      homN (Y.U (goodOf Y.d.c₂ σ)) (xiR D) (G + (wtOf (T.Q.Dw j) u 0 - G)) (f * tw.sig) z =
        homN (Y.U (goodOf Y.d.c₂ σ)) (xiR D) G f z * tw.cInf σ := fun z hz => tw.homN_mul_sig hB f hz
  have e : goodOf Y.d.c₂ σ = σ := if_pos hσ
  rw [e, hGG] at key
  have hl := lieFacZ_pos (Dw := T.Q.Dw j) (xiR D) (wtOf (T.Q.Dw j) u 0)
  refine ⟨f * tw.sig, hmem, lieFacZ (T.Q.Dw j) (xiR D) G * tw.cInf σ / lieFacZ (T.Q.Dw j) (xiR D) (wtOf (T.Q.Dw j) u 0),
    div_pos (mul_pos (lieFacZ_pos _ _) (tw.cInf_pos σ)) hl, fun z hz => ?_⟩
  have h1 := key z hz
  unfold homN at h1
  rw [div_mul_eq_mul_div, eq_div_iff hl.ne']
  linear_combination h1

private theorem twist_thin : Hypotheses2 → HypothesesH → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ u1, Quo p i PP u1 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (σ : Y.d.c₂.F →+* ℂ), GoodEmb Y.d.c₂ σ → ∀ y : FPt (Y.U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z → ∀ f ∈ cuspW Y.d.Xo₂ Y.d.c₂ Y.U (GlobalTheory.RefSum.GOf p i u1), ∃ g ∈ cuspOn Y.U Z (wtOf (dat p i) u1 0), ∃ K : ℝ, 0 < K ∧ ∀ z : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r, z ∈ framesOn (Y.U σ) Z → ptN (modelWt (Y.U σ) (wtOf (dat p i) u1 0)) (rdU (Y.U σ) g) z = K * ptN (modelWt (Y.U σ) (GlobalTheory.RefSum.GOf p i u1)) (rdU (Y.U σ) f) z := by
  intro hP _ _ hS hFD
  have R := GlobalTheory.T.weight_conditions_at_index
  have F := GlobalTheory.T.flat_line_c1_log_bound hFD
  have Q := GlobalTheory.RefSum.QuoShape.quo_shape hS
  unfold Covers Lifts at *
  refine (R.and (F.and Q)).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C1, h1, e1⟩, ⟨C2, h2, e2⟩, ⟨C3, h3, e3⟩⟩ := h
  refine ⟨C1, h1, ?_⟩
  obtain ⟨x0, hx0⟩ := e1.and (e2.and e3)
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨hA, hB, hC⟩ := hx0 x hx hle ι p hp
  obtain ⟨hL, -, -, -, hj, -⟩ := hA i hi
  have hFl := (hB i hi Y hY).2.2.1
  intro u1 hq Z σ hσ _ _ f hf
  obtain ⟨-, -, -, -, -, -, -, -, hG⟩ := hC i hi u1 hq
  rw [hG] at hf ⊢
  exact exists_twist_const hP p.T _ Y _ _ hL hj hY.1 hFl u1 _ _ Z σ hσ hf

end GlobalTheory.ThinTwist

theorem _root_.GlobalTheory.T.cusp_form_bounded_on_frames : Hypotheses2 → HypothesesH → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ u1, Quo p i PP u1 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (σ : Y.d.c₂.F →+* ℂ), GoodEmb Y.d.c₂ σ → ∀ y : FPt (Y.U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z → ∀ f ∈ cuspW Y.d.Xo₂ Y.d.c₂ Y.U (GlobalTheory.RefSum.GOf p i u1), ∃ g ∈ cuspOn Y.U Z (wtOf (dat p i) u1 0), ∃ K : ℝ, 0 < K ∧ ∀ z : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r, z ∈ framesOn (Y.U σ) Z → ptN (modelWt (Y.U σ) (wtOf (dat p i) u1 0)) (rdU (Y.U σ) g) z = K * ptN (modelWt (Y.U σ) (GlobalTheory.RefSum.GOf p i u1)) (rdU (Y.U σ) f) z := GlobalTheory.ThinTwist.twist_thin
