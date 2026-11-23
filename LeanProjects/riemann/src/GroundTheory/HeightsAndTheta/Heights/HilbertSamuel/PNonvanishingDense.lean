import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNonvanishingDense
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRatPrimeDense
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem NonvanishingDense.aeval_map_rat {σ : Type} (z : σ → ℂ) (g : MvPolynomial σ ℤ) :
    aeval z (map (Int.castRingHom ℚ) g) = eval z (map (Int.castRingHom ℂ) g) := by
  rw [aeval_def, eval₂_map, eval_map]
  congr 1

theorem NonvanishingDense.proof (h : RatPrimeDense.Statement) : NonvanishingDense.Statement := by
  intro K _ ι _ P d f hP hf z hz
  obtain ⟨_, ⟨hprime, -, -⟩, hhor, -⟩ := hP
  let _ : Algebra (MvPolynomial (Σ k, ι k) ℤ) (MvPolynomial (Σ k, ι k) ℚ) := algebraMvPolynomial
  have hφ : ∀ g, algebraMap (MvPolynomial (Σ k, ι k) ℤ) (MvPolynomial (Σ k, ι k) ℚ) g =
      map (Int.castRingHom ℚ) g := fun g => by
    change map (algebraMap ℤ ℚ) g = _
    congr 1
  have hdisj : Disjoint ((nonZeroDivisors ℤ).map (C (σ := Σ k, ι k)) : Set (MRing ι)) ↑P := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, hn, rfl⟩ hnP
    have : n ∈ P.comap (C : ℤ →+* MRing ι) := hnP
    rw [hhor, Ideal.mem_bot] at this
    exact nonZeroDivisors.ne_zero hn this
  set Pq := Ideal.map (algebraMap (MvPolynomial (Σ k, ι k) ℤ) (MvPolynomial (Σ k, ι k) ℚ)) P
  have hPq : Pq.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint ((nonZeroDivisors ℤ).map C) _ P hprime hdisj
  have hunder : Pq.comap (algebraMap _ _) = P :=
    IsLocalization.under_map_of_isPrime_disjoint ((nonZeroDivisors ℤ).map C) _ hprime hdisj
  have hfq : map (Int.castRingHom ℚ) f ∉ Pq := fun h' => hf (by
    rw [← hunder, Ideal.mem_comap, hφ]; exact h')

  have hzero : ∀ w : (Σ k, ι k) → ℂ, (∀ g ∈ P, eval w (map (Int.castRingHom ℂ) g) = 0) →
      ∀ g ∈ Pq, aeval w g = 0 := by
    intro w hw g hg
    have hle : Pq ≤ RingHom.ker (aeval w : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] ℂ).toRingHom := by
      refine Ideal.map_le_iff_le_comap.mpr fun g' hg' => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker, hφ]
      change aeval w (map (Int.castRingHom ℚ) g') = 0
      rw [NonvanishingDense.aeval_map_rat]
      exact hw g' hg'
    exact hle hg
  have hz' : z ∈ closure {w : (Σ k, ι k) → ℂ | (∀ g ∈ Pq, aeval w g = 0) ∧
      aeval w (map (Int.castRingHom ℚ) f) ≠ 0} := h _ Pq _ hPq hfq (hzero z hz.2)
  have hU : IsOpen {w : (Σ k, ι k) → ℂ | ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0} := by
    simp only [Set.ofPred_forall, Set.ofPred_exists]
    exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  refine closure_mono ?_ (hU.inter_closure ⟨hz.1, hz'⟩)
  rintro w ⟨hwU, hwP, hwf⟩
  refine ⟨⟨hwU, fun g hg => ?_⟩, ?_⟩
  · rw [← NonvanishingDense.aeval_map_rat, ← hφ]
    exact hwP _ (Ideal.mem_map_of_mem _ hg)
  · rwa [← NonvanishingDense.aeval_map_rat]

end GroundTheory.Heights₂.Heights.HilbertSamuel
