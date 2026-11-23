import Formalism.SharpRestriction.CuspSpanNormBounds.IsPtRepTrDat

open MeasureTheory Matrix Finset

noncomputable section

set_option linter.unusedVariables false

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

theorem frame_bound_of_bessel_torus_consts (D : D7) (Ch Aw Cg Cg1 Cq C1 CardSubmodulesOfIndexLePow C2 Cs CA CQ Cb Cb1 Cb2 Cgf1 Cgf Cf : ℝ)
    (K : Formalism.MainNotions.TheoremBConstants.WeightedBoundConstants Ch Aw Cg Cg1 Cq C1 CardSubmodulesOfIndexLePow C2 Cs CA CQ Cb Cb1 Cb2 Cgf1 Cgf Cf) (hCf : 2 ≤ Cf)
    (hOB : OneBesselTor D Cgf1) : FrameBesselBound D Cgf1 Cf := by
  intro L f κ₀ κ τ hκ₀ hκ hτ hc hκN hκNt hε hgap hf
  obtain ⟨f₁, C, hC, hf₁, hJ, hO⟩ := hOB L f κ₀ κ τ hκ₀ hκ hτ hc hκN hκNt hε hgap hf
  have hk2 : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hk1 : 1 ≤ D.R.k := by omega
  have hCpos : 0 < ‖C‖ := norm_pos_iff.mpr hC
  have e1 : Tz D.R.k D.R.rS (trDat L κ τ hκ hτ).z = τ ^ 2 * Tz D.R.k D.R.rS L.z := Tz_smul _ _
  have e2 : Tz D.R.k D.R.rS (trDat L κ τ hκ hτ).z' = τ ^ 2 * Tz D.R.k D.R.rS L.z' := Tz_smul _ _
  refine ⟨trDat L κ τ hκ hτ, f₁, rfl, rfl, rfl, rfl, ?_, ?_, ?_, e1, e2, hf₁, ?_⟩
  · show (κ : ℂ) * L.c = _
    rw [hc]; unfold cOfDpsi; push_cast; ring
  · show 0 < L.κN * ENNReal.ofReal (deltaN D.R.k D.R.rS κ τ)
    exact ENNReal.mul_pos hκN.ne' (ENNReal.ofReal_pos.mpr (deltaN_pos hκ hτ)).ne'
  · show L.κN * ENNReal.ofReal (deltaN D.R.k D.R.rS κ τ) ≠ ⊤
    exact ENNReal.mul_ne_top hκNt ENNReal.ofReal_ne_top
  intro μsec hsec
  refine ⟨secTr τ μsec, isSection_tr hτ hsec, jacBig D.R.rS κ τ * wBig D.R.k D.R.rS κ τ * ‖C‖ ^ 2,
    mul_pos (mul_pos (jacBig_pos hκ hτ) (wBig_pos hκ hτ)) (pow_pos hCpos 2), ?_, ?_⟩
  · refine jNorm2_tr hκ hτ L (trDat L κ τ hκ hτ) e1 e2 f f₁ μsec (secTr τ μsec) C hk2 fun p hp hζ => ?_
    rw [secTr_sBig hτ]
    have hb : bigCell D.R.k D.R.rS (sBig D.R.rS κ τ p).1 (μsec p.2) =
        cj D.R.k D.R.rS κ τ (bigCell D.R.k D.R.rS p.1 (μsec p.2)) := by
      rw [bigCell_cj hκ hτ]; rfl
    rw [hb]
    show @hsNormSq L.Wp L.Wq _ _ _ _ _
      ((trDat L κ τ hκ hτ).J f₁ (cj D.R.k D.R.rS κ τ (bigCell D.R.k D.R.rS p.1 (μsec p.2)))) = _
    rw [J_trD hκ hτ L, hJ p.1 (μsec p.2) hp (hsec.2 p.2 hζ).1, hsNormSq_smul]
  · intro γ hG
    refine ⟨ptTr κ τ hκ hτ γ, rfl, ?_, ?_⟩
    · rw [e1, e2, GPoint_ptTr]
    · rw [e1, e2, orbSq_trDat hκ hτ L f f₁ γ C fun g μR ν h1 h2 h3 h4 => hO γ g μR ν hG h1 h2 h3 h4]
      have hα := alphaPt_pos hκ hτ γ
      have hw := ptWeight_ptTr hk1 hκ hτ (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ
      have hcard := card_rootPat_le γ
      refine frames_ineqs (orbSq L f γ) (by positivity)
        (mul_pos (mul_pos (jacBig_pos hκ hτ) (wBig_pos hκ hτ)) (pow_pos hCpos 2)).le (inv_pos.mpr (by positivity))
        (ratio_le_frameFactor hκ hτ hCf hcard) (by rw [inv_inv]; exact ratio_inv_le_frameFactor hκ hτ hCf hcard) ?_
      have hP : 0 < κ ^ (2 * (rootPat γ).card) := pow_pos hκ _
      have hpw : ptWeight D.R.k D.R.rS (τ ^ 2 * Tz D.R.k D.R.rS L.z) (τ ^ 2 * Tz D.R.k D.R.rS L.z')
          (ptTr κ τ hκ hτ γ) = Wbig D.R.k D.R.rS κ τ * alphaPt κ τ γ ^ 2 *
            ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ / κ ^ (2 * (rootPat γ).card) := by
        rw [eq_div_iff hP.ne']; exact hw
      rw [hpw, wBig_eq_Wbig hk1, jacBig_eq, pow_add]
      field_simp

end Formalism.MainNotions.FrameBoundFromBesselTorus
