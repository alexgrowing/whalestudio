import Mathlib
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LossSumPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertLossPrimeSum

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

namespace GlobalTheory.InertLossAdm

theorem inertPrimes_loss_log_sum_admissible : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, Formalism.MainNotions.WeightDegreeSizes.InertPrimeLossBound (Fm.D x i) (Fm.L x i) Fm.GK Fm.cX.err C := by
  intro eps Fm h0 h1
  obtain ⟨C1, x1, hC1, hc⟩ := GlobalTheory.ConjLossPrimes.loss_sum_primes Fm h0 h1
  obtain ⟨C2, x2, hC2, hi⟩ := GlobalTheory.OtherLoss.inertLoss_primeSum Fm h0 h1
  refine ⟨C1 + C2, max x1 x2, add_nonneg hC1 hC2, ?_⟩
  intro x hx hx1 i j hj P hP
  rw [← Finset.sum_filter_add_sum_filter_not P
    (fun p => G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0)]
  have A := hc x (le_trans (le_max_left _ _) hx) hx1 i j hj (P.filter
    (fun p => G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0))
    (fun p hp => by
      rw [Finset.mem_filter] at hp
      exact ⟨(hP p hp.1).1, (hP p hp.1).2.2⟩)
  have B := hi x (le_trans (le_max_right _ _) hx) hx1 i j hj (P.filter
    (fun p => ¬ (G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0)))
    (fun p hp => by
      rw [Finset.mem_filter] at hp
      exact ⟨(hP p hp.1).1, (hP p hp.1).2.1, (hP p hp.1).2.2, hp.2⟩)
  have eA : ∑ p ∈ P.filter (fun p => G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0),
      2 * Real.log (p : ℝ) * |Formalism.MainNotions.WeightDegreeSizes.EatCI (Fm.L x i) Fm.GK Fm.cX.err j p| =
      ∑ p ∈ P.filter (fun p => G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0),
      2 * Real.log (p : ℝ) * |EatC (Fm.L x i) Fm.cX.err j p| := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_filter] at hp
    unfold Formalism.MainNotions.WeightDegreeSizes.EatCI
    rw [if_pos hp.2]
  have eB : ∑ p ∈ P.filter (fun p => ¬ (G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0)),
      2 * Real.log (p : ℝ) * |Formalism.MainNotions.WeightDegreeSizes.EatCI (Fm.L x i) Fm.GK Fm.cX.err j p| =
      ∑ p ∈ P.filter (fun p => ¬ (G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0)),
      2 * Real.log (p : ℝ) * |EatI (Fm.L x i) Fm.GK Fm.cX.err j p| := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_filter] at hp
    unfold Formalism.MainNotions.WeightDegreeSizes.EatCI
    rw [if_neg hp.2]
  rw [eA, eB, add_mul]
  exact add_le_add A B

end GlobalTheory.InertLossAdm
