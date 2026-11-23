import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsEnd
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

theorem tauSum_rearrangement {ι : Type*} (s : Finset ι) (a c e : ℝ) (al be sh tot : ι → ℝ) :
    ∑ τ ∈ s, (((a - al τ) - (c - be τ)) * sh τ + (e - be τ) * tot τ) =
      (a - c) * ∑ τ ∈ s, sh τ + e * ∑ τ ∈ s, tot τ - ∑ τ ∈ s, (al τ - be τ) * sh τ -
        ∑ τ ∈ s, be τ * tot τ := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun τ _ => by ring

theorem HeightSumIdentity.proof : HeightSumIdentity.Statement := by
  intro d S hS B0
  obtain ⟨B1, CE, hcor⟩ := hS.corB
  obtain ⟨CA, hA⟩ := hS.propA
  refine ⟨max B1 2, fun F Q hFQ => ?_⟩
  have hF : F.IsHomogeneous (d.D + 1) := hFQ.1
  refine ⟨S.vol * ((∑ τ : Fin d.f, (2 * |(shiftFl d τ F : ℝ)| + |(totalFl d τ F : ℝ)|)) * CA) +
      (∑ m ∈ F.support, |((F.coeff m : ℚ) : ℝ)|) * CE, fun B hB0 hB => ?_⟩
  have hB1 : B1 ≤ B := le_of_max_le_left hB
  have hB2 : 2 ≤ B := le_of_max_le_right hB

  have hadd := hS.additivity B0 B hB0 F hF
  have hsum : ∑ p ∈ primesIn S B0 B, S.delta p F =
      -(∑ p ∈ primesIn S B0 B, Real.log p / ((p : ℝ) - 1)) * S.vol * (shSum d F : ℝ) +
        (∑ p ∈ primesIn S B0 B, kaNum S p * Real.log p) / (d.N : ℝ) * S.vol * (totSum d F : ℝ) +
        ∑ p ∈ primesIn S B0 B, rest₂ d S.vol p (S.frob p) Q := by
    rw [Finset.sum_congr rfl (fun p hp => by
      simp only [primesIn, Finset.mem_filter] at hp
      exact hS.eq81 p hp.2.1 hp.2.2 F Q hFQ)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [Finset.sum_mul, Finset.sum_div, Finset.sum_neg_distrib, neg_mul]
  have hcorB := (hcor B hB1).1 F hF
  have key : S.PP B0 F - (S.vol * (S.hh F - aB S B0 B * (shSum d F : ℝ) -
        bB S B0 B * (totSum d F : ℝ)) + ∑ p ∈ primesIn S B0 B, rest₂ d S.vol p (S.frob p) Q) =
      S.vol * ∑ τ : Fin d.f, (((S.alC B - S.al B τ) - (S.beC B - S.be B τ)) *
          (shiftFl d τ F : ℝ) + (S.beC B - S.be B τ) * (totalFl d τ F : ℝ)) + S.EE B F := by
    rw [tauSum_rearrangement, hadd, hsum, hcorB]
    simp only [aB, bB, shSum, totSum, Rat.cast_sum]
    ring
  rw [key]
  have hL0 : 0 ≤ Real.log B / B := div_nonneg (Real.log_nonneg (by exact_mod_cast
    (show 1 ≤ B by omega))) (Nat.cast_nonneg B)
  have hT : |∑ τ : Fin d.f, (((S.alC B - S.al B τ) - (S.beC B - S.be B τ)) *
        (shiftFl d τ F : ℝ) + (S.beC B - S.be B τ) * (totalFl d τ F : ℝ))| ≤
      (∑ τ : Fin d.f, (2 * |(shiftFl d τ F : ℝ)| + |(totalFl d τ F : ℝ)|)) * CA *
        (Real.log B / B) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun τ _ => ?_
    obtain ⟨ha, hb⟩ := hA B hB2 τ
    have h1 : |S.alC B - S.al B τ| ≤ CA * (Real.log B / B) := by
      rw [abs_sub_comm, ← mul_div_assoc]; exact ha
    have h2 : |S.beC B - S.be B τ| ≤ CA * (Real.log B / B) := by
      rw [abs_sub_comm, ← mul_div_assoc]; exact hb
    calc _ ≤ |((S.alC B - S.al B τ) - (S.beC B - S.be B τ)) * (shiftFl d τ F : ℝ)| +
          |(S.beC B - S.be B τ) * (totalFl d τ F : ℝ)| := abs_add_le _ _
      _ = |(S.alC B - S.al B τ) - (S.beC B - S.be B τ)| * |(shiftFl d τ F : ℝ)| +
          |S.beC B - S.be B τ| * |(totalFl d τ F : ℝ)| := by rw [abs_mul, abs_mul]
      _ ≤ (|S.alC B - S.al B τ| + |S.beC B - S.be B τ|) * |(shiftFl d τ F : ℝ)| +
          |S.beC B - S.be B τ| * |(totalFl d τ F : ℝ)| := by gcongr; exact abs_sub _ _
      _ ≤ (CA * (Real.log B / B) + CA * (Real.log B / B)) * |(shiftFl d τ F : ℝ)| +
          CA * (Real.log B / B) * |(totalFl d τ F : ℝ)| := by gcongr
      _ = _ := by ring
  have hEE : |S.EE B F| ≤ (∑ m ∈ F.support, |((F.coeff m : ℚ) : ℝ)|) * CE * (Real.log B / B) := by
    conv_lhs => rw [F.as_sum]
    rw [map_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun m hm => ?_
    have hdeg : (m.sum fun _ e => e) = d.D + 1 := by
      have := hF (mem_support_iff.mp hm)
      simpa [Finsupp.weight_apply] using this
    have hmono := (hcor B hB1).2 m hdeg
    rw [show monomial m (F.coeff m) = (F.coeff m) • monomial m (1 : ℚ) by
      rw [smul_monomial, smul_eq_mul, mul_one], map_smul, Rat.smul_def, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (by rw [← mul_div_assoc]; exact hmono) (abs_nonneg _)
  calc _ ≤ |S.vol * ∑ τ : Fin d.f, (((S.alC B - S.al B τ) - (S.beC B - S.be B τ)) *
          (shiftFl d τ F : ℝ) + (S.beC B - S.be B τ) * (totalFl d τ F : ℝ))| + |S.EE B F| :=
        abs_add_le _ _
    _ = S.vol * |∑ τ : Fin d.f, (((S.alC B - S.al B τ) - (S.beC B - S.be B τ)) *
          (shiftFl d τ F : ℝ) + (S.beC B - S.be B τ) * (totalFl d τ F : ℝ))| + |S.EE B F| := by
        rw [abs_mul, abs_of_pos S.vol_pos]
    _ ≤ S.vol * ((∑ τ : Fin d.f, (2 * |(shiftFl d τ F : ℝ)| + |(totalFl d τ F : ℝ)|)) * CA *
          (Real.log B / B)) + (∑ m ∈ F.support, |((F.coeff m : ℚ) : ℝ)|) * CE * (Real.log B / B) :=
        add_le_add (mul_le_mul_of_nonneg_left hT S.vol_pos.le) hEE
    _ = _ := by ring

end GroundTheory.Heights₂.Heights.TheoremB
