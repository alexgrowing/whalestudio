import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLc
import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLe
import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLf
import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLn
import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLo
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSl
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSaa
import Formalism.SharpRestriction.AdmissibleParameterJoins.NandDIVi
import Formalism.SharpRestriction.AdmissibleParameterJoins.NandDIVq
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.CMFieldLemmas
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Formalism.SharpRestriction.Divisibility.SlopeExcess.ExcSplitOfGMod

noncomputable section

namespace Formalism.MainNotions.Pk

open Formalism.BasicNotions Formalism.BasicNotions.DV

section Family

variable {eps : ℝ} (Fm : FamP eps)

theorem dlSizeF : J.DlSize Fm :=
  ⟨Fm.x1 + 1, fun x hx i => (Fm.sizes x (lt_of_lt_of_le (lt_add_one _) hx) i).2.2.2.2.2.2.1.2.2.2.2.2.1⟩

theorem settingF (hT : TuSize Fm) (hDl : J.DlSize Fm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, product_first_zeroth_parts.HidaSetting (Fm.D x i) u := by
  obtain ⟨Cn, hN⟩ := J.numsL_wtsL_fam Fm hT hDl
  obtain ⟨x0, hN⟩ := hN Cn le_rfl 3 le_rfl
  obtain ⟨x1, hT⟩ := hT
  obtain ⟨x3, h3⟩ := flipTwoThree.le_rpow_for_large_x ((2 : ℝ) / 5) (by norm_num) 4
  refine ⟨max (max x0 x1) (max x3 (max 4 (Fm.x1 + 1))), fun x hx i u => ?_⟩
  have e0 : x ≥ x0 := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have e1 : x ≥ x1 := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have e3 : x3 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have e4 : 4 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hx
  have e5 : Fm.x1 < x := by
    have := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hx
    linarith
  have hsx : (Fm.L x i).sc.x = x := Fm.L_x x i e5
  have hm : 4 ≤ (Fm.D x i).R.m := by
    have z1 := (flipTwoThree.size_bounds_of_scale (Fm.L x i) (Fm.sizes x e5 i) (by rw [hsx]; exact e4)).1
    rw [hsx] at z1
    have : (4 : ℝ) ≤ (Fm.D x i).R.m := le_trans (h3 x e3) z1
    exact_mod_cast this
  exact J.levelPrime_setting_of_sizes le_rfl (hN x e0 i).1 (hN x e0 i).2 (hT x e1 i).1 hm u

theorem proved_level_prime_large_scale {crystallineComparison : ℝ} (hT : TuSize Fm) (hDl : J.DlSize Fm) (h : product_first_zeroth_parts.ConclusionOnFamily Fm crystallineComparison) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, product_first_zeroth_parts.Conclusion₂ (Fm.D x i) u crystallineComparison := by
  obtain ⟨a, ha⟩ := settingF Fm hT hDl
  obtain ⟨b, hb⟩ := h
  exact ⟨max a b, fun x hx i u => hb x (le_trans (le_max_right _ _) hx) i u (ha x (le_trans (le_max_left _ _) hx) i u)⟩

def LevelPrimeItems (crystallineComparison : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word), product_first_zeroth_parts.HidaSetting (Fm.D x i) u →
    product_first_zeroth_parts.Conclusion2 (Fm.D x i) u ∧ product_first_zeroth_parts.Conclusion5 (Fm.D x i) u crystallineComparison ∧ product_first_zeroth_parts.Conclusion6 (Fm.D x i) u ∧ product_first_zeroth_parts.Conclusion5Sharp (Fm.D x i) u

theorem levelPrimeItems_of_proved {crystallineComparison : ℝ} (h : product_first_zeroth_parts.ConclusionOnFamily Fm crystallineComparison) : LevelPrimeItems Fm crystallineComparison := by
  obtain ⟨x0, h⟩ := h
  exact ⟨x0, fun x hx i u hs => ⟨(h x hx i u hs).2.1, (h x hx i u hs).2.2.2.2.1, (h x hx i u hs).2.2.2.2.2.1,
    (h x hx i u hs).2.2.2.2.2.2.2.2⟩⟩

theorem level_prime_items_large_scale {crystallineComparison : ℝ} (hT : TuSize Fm) (hDl : J.DlSize Fm) (h : LevelPrimeItems Fm crystallineComparison) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, product_first_zeroth_parts.Conclusion2 (Fm.D x i) u ∧ product_first_zeroth_parts.Conclusion5 (Fm.D x i) u crystallineComparison ∧ product_first_zeroth_parts.Conclusion6 (Fm.D x i) u ∧
      product_first_zeroth_parts.Conclusion5Sharp (Fm.D x i) u := by
  obtain ⟨a, ha⟩ := settingF Fm hT hDl
  obtain ⟨b, hb⟩ := h
  exact ⟨max a b, fun x hx i u => hb x (le_trans (le_max_right _ _) hx) i u (ha x (le_trans (le_max_left _ _) hx) i u)⟩

theorem admissible_sum_over_primes (h : LinkG Fm) : LocalQuadraticParts.LogTermFamily Fm := by
  obtain ⟨C, x0, δ, hδ, H⟩ := h
  refine ⟨C, x0, δ, hδ, fun x hx i => ?_⟩
  intro w hw hin _
  obtain ⟨_, _, h3, _, _⟩ := H x hx i
  exact h3 w hin hw

structure ExtC (C3 crystallineComparison : ℝ) : Prop where

  linkG : LinkG Fm

  g69 : AuxBlock8.ConclusionOnFamily Fm Fm.GK Fm.Gx
  localLemmaThreeThreeTwo : CornerGLContinuity.FamilyOrdersLargePrimeBoundConstant Fm
  g32 : CornerGLContinuity.FamilyBadPrimeBound Fm
  gTauSz : CornerGLContinuity.FamilyCutSizes Fm
  gTa : CornerGLContinuity.FamilyWeightSumBound Fm
  n33 : ArithmeticCylinders.FamilyExpDeficitBound' Fm

  gl23 : flipTwoThree.ConclusionF5 Fm ∧ flipTwoThree.ConclusionF6 Fm

  gl24 : StandardLattice.FamilyPartFour Fm C3 ∧ StandardLattice.PartFiveFamilyBounds Fm

  gl10 : LevelPrimeItems Fm crystallineComparison
  nuFull : NuFullF Fm

  n56 : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), ∃ (HW : HWOf (Fm.D x i).loc)
    (F : FonOf (Fm.D x i).loc (Fm.D x i).locA HW) (Cm : CmpOf (Fm.D x i).loc (Fm.D x i).locA HW F),
    DeltaInvariantLattices.aux₃ (Fm.D x i) HW F Cm ∧ DeltaInvariantLattices.ConclusionE (Fm.D x i) HW F

structure BrC : Prop where

  colVal : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u)
  br25 : ∃ C0 : ℝ, ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, J.RankHyp (Fm.D x i) ∧
    ∃ Δ : ℝ, StandardLattice.DataB (Fm.D x i) (Fm.L x i).sc C0 Δ (fun j ρ => wSz (Fm.D x i) (j + 1) ρ)

variable {Fm}

theorem admissible_top_line_family {C3 crystallineComparison C0 CH : ℝ} (E : ExtC Fm C3 crystallineComparison) (B : BrC Fm) (hCh : ChosenE Fm C0 CH) (hT : TuSize Fm)
    (hTw : TwGood Fm) : LocalQuadraticParts.AdmCF Fm := by
  have hDl := dlSizeF Fm
  obtain ⟨Cb, x25, h25⟩ := B.br25
  obtain ⟨x10, h10⟩ := level_prime_items_large_scale Fm hT hDl E.gl10
  obtain ⟨C₅, h59⟩ := UnusedSlot33.field_lemmas_except_seven
  obtain ⟨xD, hD⟩ := hDl
  refine ⟨J.full_rank_family_of_eventually_nuFull Fm E.nuFull, J.family_served_prime_lattices Fm E.linkG, admissible_sum_over_primes Fm E.linkG,
    J.family_served_orbits_band Fm E.localLemmaThreeThreeTwo E.g32, J.family_scale_epsilon_condition Fm E.n33,
    J.family_logDerivative_regulator_bound Fm ⟨xD, fun x hx i => ⟨hD x hx i, by linarith [flipTwoThree.two_le_rdE (Fm.D x i).host]⟩⟩,
    J.slopes_family_of_column_values Fm hT ⟨xD, hD⟩ E.gl23.1 E.gl23.2 B.colVal,
    J.family_rank_count_bound Fm Cb (fun x hx i => (E.gl24.1 x hx i).2.2.2.2.2.2.2.1) E.gl24.2
      ⟨max x25 (Fm.x1 + 1), fun x hx i => ?_⟩,
    J.family_levelPrime_summary_closed Fm crystallineComparison hT ⟨xD, hD⟩ ⟨x10, fun x hx i => ⟨fun u => (h10 x hx i u).1,
      fun u => (h10 x hx i u).2.1⟩⟩,
    J.family_sizes_depths_thresholds Fm E.gTauSz E.gTa (DIV.Proofs.excSplit_large Fm), J.family_good_twists_condition Fm hTw, J.family_mean_shares_windows Fm E.g69, J.family_served_orbit_counts_agree Fm, J.orbits_and_orders_hold,
    J.family_dyadic_order_consequences Fm 100 (fun x i => (h59 (Fm.D x i) (Fm.L x i).sc).2.2.2.1), J.lemma_on_tops_holds,
    J.family_four_choice_conditions Fm C0 CH hCh, J.family_bad_choice_bound Fm C0 CH hCh⟩
  have e5 : Fm.x1 < x := by
    have := le_trans (le_max_right _ _) hx
    linarith
  obtain ⟨a, b⟩ := h25 x (le_trans (le_max_left _ _) hx) i
  exact ⟨(Fm.sizes x e5 i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, a, b⟩

end Family

end Formalism.MainNotions.Pk

end
