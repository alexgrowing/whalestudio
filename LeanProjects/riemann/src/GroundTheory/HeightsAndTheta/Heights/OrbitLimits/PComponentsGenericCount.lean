import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StComponentsGenericCount
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PComponentsPairPoly
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

namespace ComponentsGenericCount

theorem proof : ComponentsGenericCount.Statement := by
  classical
  intro n d F A hF hinc
  have hfib : ∀ y, {x | (∃ J ∈ F, x ∈ zeroSet J) ∧ A *ᵥ x = y} = ⋃ J ∈ F, fibre J A y := by
    intro y; ext x; simp only [fibre, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]; tauto
  have hcard : ∀ J ∈ F, ∀ y, (fibre J A y).encard ≤ (projDegree J A : ℕ∞) := by
    intro J hJ y
    obtain ⟨-, hfin, hle⟩ := ComplexSets.FibreBound.full n d J A (hF J hJ).1 (hF J hJ).2.1 (hF J hJ).2.2 y
    rw [← hfin.cast_ncard_eq]; exact_mod_cast hle
  refine ⟨fun y => ?_, ?_⟩
  · rw [hfib, Nat.cast_sum]
    exact (encard_biUnion_le F _).trans (Finset.sum_le_sum fun J hJ => hcard J hJ y)
  obtain ⟨Δ₁, hΔ₁, hΔ₁y⟩ := exists_prod_ne_zero F
    (fun J P => ∀ y, eval y P ≠ 0 → (fibre J A y).Finite ∧ (fibre J A y).ncard = projDegree J A ∧
      ∀ x ∈ fibre J A y, ∃ (U : Set (Fin d → ℂ)) (g : (Fin d → ℂ) → Fin n → ℂ), IsOpen U ∧ y ∈ U ∧
        DifferentiableOn ℂ g U ∧ g y = x ∧ ∀ y' ∈ U, A *ᵥ g y' = y' ∧ g y' ∈ zeroSet J)
    (fun J hJ => by
      obtain ⟨P, hP, hPy⟩ :=
        ComplexSets.DiscriminantCover.full n d J A (hF J hJ).1 (hF J hJ).2.1 (hF J hJ).2.2
      refine ⟨P, hP, fun y hy => ?_⟩
      obtain ⟨hfin, hc, hsec⟩ := hPy y hy
      refine ⟨hfin, hc, fun x hx => ?_⟩
      obtain ⟨U, V, g, hU, hyU, -, -, hg, hgx, hAg, hZ⟩ := hsec x hx
      refine ⟨U, g, hU, hyU, hg, hgx, fun y' hy' => ⟨hAg y' hy', ?_⟩⟩
      have hmem : g y' ∈ zeroSet J ∩ V := hZ ▸ Set.mem_image_of_mem g hy'
      exact hmem.1)
  obtain ⟨Δ₂, hΔ₂, hΔ₂y⟩ := exists_prod_ne_zero ((F ×ˢ F).filter fun p => p.1 ≠ p.2)
    (fun p c => ∀ x ∈ zeroSet p.1, x ∈ zeroSet p.2 → eval (A *ᵥ x) c = 0)
    (fun p hp => by
      simp only [Finset.mem_filter, Finset.mem_product] at hp
      exact exists_pair_poly p.1 p.2 A (hF _ hp.1.1).1 (hF _ hp.1.1).2.2
        fun h => hp.2 (hinc _ hp.1.2 _ hp.1.1 h).symm)
  refine ⟨Δ₁ * Δ₂, mul_ne_zero hΔ₁ hΔ₂, fun y hy => ?_⟩
  rw [map_mul] at hy
  have h1 := hΔ₁y y (left_ne_zero_of_mul hy)
  have h2 := hΔ₂y y (right_ne_zero_of_mul hy)
  refine ⟨?_, ?_⟩
  · rw [hfib, Nat.cast_sum, encard_biUnion_eq]
    · refine Finset.sum_congr rfl fun J hJ => ?_
      obtain ⟨P, hP, hPy⟩ := h1 J hJ
      obtain ⟨hfin, hc, -⟩ := hP y hPy
      rw [← hfin.cast_ncard_eq, hc]
    · intro J hJ J' hJ' hne
      rw [Set.disjoint_left]
      rintro x ⟨hxJ, hxy⟩ ⟨hxJ', -⟩
      obtain ⟨c, hc, hcy⟩ := h2 (J, J') (by simp [hJ, hJ', hne])
      exact hcy (by rw [← hxy]; exact hc x hxJ hxJ')
  · rintro x ⟨J, hJ, hxJ⟩ hxy
    obtain ⟨P, hP, hPy⟩ := h1 J hJ
    obtain ⟨U, g, hU, hyU, hg, hgx, hsec⟩ := (hP y hPy).2.2 x ⟨hxJ, hxy⟩
    exact ⟨U, g, hU, hyU, hg, hgx, fun y' hy' => ⟨(hsec y' hy').1, J, hJ, (hsec y' hy').2⟩⟩

end ComponentsGenericCount

end GroundTheory.Heights₂.Heights
