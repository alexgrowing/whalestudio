import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
open GlobalTheory.EtC

namespace GlobalTheory.AICIff
open Polynomial

theorem root_mem_range {D K : Type} [CommRing D] [Nontrivial D] [CommRing K] [IsDomain K] [Algebra D K]
    (h : AIC D) : ∀ (n : ℕ) (p : D[X]), p.Monic → p.natDegree = n →
      ∀ x : K, aeval x p = 0 → ∃ y : D, algebraMap D K y = x := by
  intro n
  induction n with
  | zero =>
    intro p hp hn x hx
    rw [eq_one_of_monic_natDegree_zero hp hn] at hx
    simp at hx
  | succ n ih =>
    intro p hp hn x hx
    obtain ⟨a, ha⟩ := h p hp (by omega)
    have hfac : (X - C a) * (p /ₘ (X - C a)) = p := (mul_divByMonic_eq_iff_isRoot).2 ha
    have hq : (p /ₘ (X - C a)).Monic := (monic_X_sub_C a).of_mul_monic_left (hfac.symm ▸ hp)
    have hqn : (p /ₘ (X - C a)).natDegree = n := by
      have := (monic_X_sub_C a).natDegree_mul hq
      rw [hfac, natDegree_X_sub_C] at this
      omega
    rw [← hfac, map_mul] at hx
    rcases mul_eq_zero.1 hx with h0 | h0
    · refine ⟨a, ?_⟩
      simp only [map_sub, aeval_X, aeval_C] at h0
      exact (sub_eq_zero.1 h0).symm
    · exact ih _ hq hqn x h0

theorem aic_iff : ∀ (D : Type) [CommRing D] [IsDomain D],
    AIC D ↔ (IsIntegrallyClosed D ∧ IsAlgClosed (FractionRing D)) := by
  intro D _ _
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [isIntegrallyClosed_iff (FractionRing D)]
      rintro x ⟨p, hp, hx⟩
      exact root_mem_range h _ p hp rfl x (by rwa [aeval_def])
    · apply IsAlgClosed.of_exists_root
      intro f hf hirr
      have hdeg : 0 < f.natDegree :=
        hf.natDegree_pos.2 (fun h1 => hirr.not_isUnit (h1 ▸ isUnit_one))
      have hinj := IsFractionRing.injective D (FractionRing D)
      obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors D) f
      set g := IsLocalization.integerNormalization (nonZeroDivisors D) f with hg
      have hc : algebraMap D (FractionRing D) (b : D) ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
      have hgmap : g.map (algebraMap D (FractionRing D)) = C (algebraMap D (FractionRing D) (b : D)) * f := by
        rw [hb, Algebra.smul_def]; rfl
      have hgdeg : g.natDegree = f.natDegree := by
        rw [← natDegree_map_eq_of_injective hinj g, hgmap, natDegree_C_mul hc]
      have hg0 : g ≠ 0 := by
        intro h0; rw [h0, natDegree_zero] at hgdeg; omega
      obtain ⟨a, ha⟩ := h (integralNormalization g) (monic_integralNormalization hg0)
        (by rw [natDegree_integralNormalization]; omega)
      have hl : algebraMap D (FractionRing D) g.leadingCoeff ≠ 0 := by
        rw [Ne, ← map_zero (algebraMap D (FractionRing D)), hinj.eq_iff]
        exact leadingCoeff_ne_zero.2 hg0
      refine ⟨algebraMap D (FractionRing D) a / algebraMap D (FractionRing D) g.leadingCoeff, ?_⟩
      have key := integralNormalization_eval₂_leadingCoeff_mul (p := g) (by omega)
        (algebraMap D (FractionRing D))
        (algebraMap D (FractionRing D) a / algebraMap D (FractionRing D) g.leadingCoeff)
      rw [mul_div_cancel₀ _ hl, eval₂_at_apply, ha, map_zero, ← eval_map, hgmap, eval_mul, eval_C] at key
      have := key.symm
      simpa [hl, hc] using this
  · rintro ⟨h1, h2⟩ p hp hpos
    have hd : (p.map (algebraMap D (FractionRing D))).degree ≠ 0 := by
      refine ne_of_gt (natDegree_pos_iff_degree_pos.1 ?_)
      rw [hp.natDegree_map]; exact hpos
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hd
    have hint : IsIntegral D x := ⟨p, hp, by rwa [IsRoot, eval_map] at hx⟩
    obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    refine ⟨y, IsFractionRing.injective D (FractionRing D) ?_⟩
    rw [map_zero, ← eval₂_at_apply, ← eval_map]
    exact hx

end GlobalTheory.AICIff
