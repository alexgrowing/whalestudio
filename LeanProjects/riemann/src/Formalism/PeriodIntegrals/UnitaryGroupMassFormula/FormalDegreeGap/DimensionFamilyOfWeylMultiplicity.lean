import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalDegreeGap.HCFdegRGapHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalDegreeGap.DimensionBoundOfGapUniform
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.PartFiveExplicitOfPropositions
import Formalism.SharpRestriction.GlobalSchurBounds.FlipTwoThree
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.HarishChandraMultiplicityBound

noncomputable section

open MeasureTheory

namespace PI.UnitaryGroupMassFormula.HCFdegRGap

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.StandardLattice

theorem dsigEx_at (D : D7) (hd : dsigTie D) (ρ : D.what₂.Tau)
    (hex : ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (H →L[ℂ] H)),
      IsDS (epsSH D.R) (lamSH D.R (D.hc ρ)) σ) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (H →L[ℂ] H)),
      IsDS (epsSH D.R) (lamSH D.R (D.hc ρ)) σ ∧
      IsFdeg ((D.s.cdScale _ (epsSH D.R) : ENNReal) • Formalism.REAL.muG (epsSH D.R)) σ (D.dsig ρ) := by
  obtain ⟨H, i1, i2, σ, hσ⟩ := hex
  haveI : CompleteSpace H := hσ.1
  obtain ⟨d, hd0, hdI⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS _ σ hσ
  have hc : (0 : ℝ) < (D.s.cdScale _ (epsSH D.R) : ℝ) := D.s.cdScale_pos _ _
  have hF : IsFdeg ((D.s.cdScale _ (epsSH D.R) : ENNReal) • Formalism.REAL.muG (epsSH D.R)) σ
      (d / (D.s.cdScale _ (epsSH D.R) : ℝ)) := by
    refine ⟨div_pos hd0 hc, fun v w v' w' => ⟨(hdI v w v' w').1.smul_measure ENNReal.coe_ne_top, ?_⟩⟩
    rw [MeasureTheory.integral_smul_measure, (hdI v w v' w').2, ENNReal.coe_toReal]
    have hc' : ((D.s.cdScale _ (epsSH D.R) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have hd' : ((d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
    rw [Complex.real_smul]
    push_cast
    field_simp
  have key := hd ρ H σ _ hσ hF
  refine ⟨H, i1, i2, σ, hσ, ?_⟩
  rw [← key]
  exact hF

theorem dimension_bound_of_scale_equalities (D : D7) (hc : cdScaleTie D) (hdt : dsigTie D) (hW : DiscreteSeriesWeylDimension.WeylForK)
    (hL : DiscreteSeriesWeylDimension.LowKMultOne) : StandardLattice.SigmaDegreeTwoSidedBoundOfGap D := by
  have hAll : StandardLattice.DiscreteSeriesDegreeBoundsOfGap D := Formalism.MainNotions.RT.theorem_three_under_scale_of_general (dimension_bound_of_gap_uniform hCFdegRGap_holds hW hL) D hc
  have hT := DiscreteSeriesWeylDimension.lowest_K_type_count_of_weyl D hW hL
  intro ep0 he1 he2 ρ hgap
  have hHC := line_param_harish_chandra D ρ
  have hp : ((Finset.univ.filter (fun a => epsSH D.R a = true)).card : ℝ) = (pY D : ℝ) := by
    have : (Finset.univ.filter (fun a => epsSH D.R a = true)).card = nPlus (epsSH D.R) := rfl
    rw [this, sign_vector_eq_line_sign, count_plus_finCast, count_plus_line_sign]
  have hq : ((Finset.univ.filter (fun a => epsSH D.R a = false)).card : ℝ) = (qY D : ℝ) := by
    have : (Finset.univ.filter (fun a => epsSH D.R a = false)).card = nMinus (epsSH D.R) := rfl
    rw [this, sign_vector_eq_line_sign, count_minus_finCast, count_minus_line_sign]
  have hN : ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) = (D.R.r : ℝ) := by rw [dimS_eq]
  have hg' : Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamSH D.R (D.hc ρ)) (spectralGapLowerBound D ep0) := by
    rw [sign_vector_eq_line_sign, param_vector_eq_line_param]; exact gapAtLeast_finCast _ _ _ _ hgap
  have hp1 : (1 : ℝ) ≤ ((Finset.univ.filter (fun a => epsSH D.R a = true)).card : ℝ) := by
    rw [hp]; exact_mod_cast (signature_counts_ge_one D).1
  have hq1 : (1 : ℝ) ≤ ((Finset.univ.filter (fun a => epsSH D.R a = false)).card : ℝ) := by
    rw [hq]; exact_mod_cast (signature_counts_ge_one D).2
  have hsum : ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) =
      ((Finset.univ.filter (fun a => epsSH D.R a = true)).card : ℝ) +
        ((Finset.univ.filter (fun a => epsSH D.R a = false)).card : ℝ) := by
    have h' := congrArg (fun x : ℕ => (x : ℝ)) (card_add_card (epsSH D.R))
    push_cast at h' ⊢
    linarith
  have hbig := gap_big (h0 := spectralGapLowerBound D ep0) hp1 hq1 hsum (by rw [hN]; exact he1) he2
    (le_of_eq (by rw [hp, hq, hN]; unfold spectralGapLowerBound; rw [Nat.cast_min]))

  have hq0 : ((ReciprocityTheory.ChartRestriction.DS.S7.q0 (epsSH D.R) : ℕ) : ℝ) ≤
      ((Finset.univ.filter (fun a => epsSH D.R a = true)).card : ℝ) := by
    have : ReciprocityTheory.ChartRestriction.DS.S7.q0 (epsSH D.R) ≤ (Finset.univ.filter (fun a => epsSH D.R a = true)).card :=
      min_le_left _ _
    exact_mod_cast this
  have hmax : max (2 * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ))
      (8 * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 (epsSH D.R) : ℝ)) < spectralGapLowerBound D ep0 := by
    generalize ((Finset.univ.filter (fun a => epsSH D.R a = true)).card : ℝ) = p at *
    generalize ((Finset.univ.filter (fun a => epsSH D.R a = false)).card : ℝ) = q at *
    generalize ((ReciprocityTheory.ChartRestriction.DS.S7.q0 (epsSH D.R) : ℕ) : ℝ) = r at *
    generalize ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) = n at *
    have hpq : 1 ≤ p * q := by nlinarith
    have hn : 1 ≤ n := by linarith
    have hrpq : r ≤ p * q := by nlinarith
    rw [max_lt_iff]
    constructor
    · nlinarith
    · nlinarith
  have hEx := dsigEx_at D hdt ρ
    (ReciprocityTheory.ChartRestriction.DS.G2.discrete_series_exists_large_gap _ (epsSH D.R) _ hHC (spectralGapLowerBound D ep0) hg' (Or.inr hmax))
  obtain ⟨H, i1, i2, σ, hDS, hF⟩ := hEx
  have hcs : CompleteSpace H := hDS.1
  have hnt : Nontrivial H := hDS.2.1
  obtain ⟨w, hw⟩ := exists_ne (0 : H)
  have hdt' := (hT _ (epsSH D.R) (lamSH D.R (D.hc ρ)) hHC H σ hDS).2
  have key := hAll _ (epsSH D.R) (lamSH D.R (D.hc ρ)) ep0 (spectralGapLowerBound D ep0) H σ w
    (by rw [hp]; exact_mod_cast (signature_counts_ge_one D).1) (by rw [hq]; exact_mod_cast (signature_counts_ge_one D).2) hHC hg'
    (by rw [hN]; exact he1) he2
    (by rw [hp, hq, hN]; unfold spectralGapLowerBound; rw [Nat.cast_min]) hDS hw
  rw [formal_degree_of_eq _ σ _ hF w hw, hp, hq, hdt'] at key
  rw [← dimV_eq_fdegHC _ hHC.1] at key
  rw [sign_vector_eq_line_sign, param_vector_eq_line_param, dim_weyl_finCast, formal_degree_finCast, abs_param_sup_finCast] at key
  refine ⟨key.1, ?_⟩
  have e : ((pY D : ℝ) * (qY D : ℝ)) = ((pY D * qY D : ℕ) : ℝ) := by push_cast; rfl
  rw [e, Real.rpow_natCast] at key
  exact key.2

theorem dimension_family_of_weyl_multiplicity {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (hW : DiscreteSeriesWeylDimension.WeylForK) (hL : DiscreteSeriesWeylDimension.LowKMultOne) :
    Formalism.MainNotions.flipTwoThree.fam0 Fm Formalism.MainNotions.StandardLattice.SigmaDegreeTwoSidedBoundOfGap := ⟨0, fun x _ _ i => dimension_bound_of_scale_equalities _ (Fm.ties x i).cdScale_tie (Fm.ties x i).dsig_tie hW hL⟩

end PI.UnitaryGroupMassFormula.HCFdegRGap
