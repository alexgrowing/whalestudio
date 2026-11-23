import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory

open Classical in
theorem coeff_prod_pow_of_embedding {σ τ R : Type} [CommRing R] (j : σ → τ) (hj : Function.Injective j)
    (a : τ → MvPowerSeries σ R) (ha : ∀ s, a (j s) = X s) (h0 : ∀ t, t ∉ Set.range j → a t = 0)
    (d : τ →₀ ℕ) (α : σ →₀ ℕ) :
    coeff α (d.prod fun t e => a t ^ e) = if d = α.mapDomain j then 1 else 0 := by
  classical
  by_cases h : ∀ t, t ∉ Set.range j → d t = 0
  · obtain ⟨β, rfl⟩ := (Finsupp.mem_range_mapDomain_iff j hj d).mpr h
    rw [Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    simp only [ha]
    rw [Finsupp.prod]
    simp only [X_pow_eq]
    rw [prod_monomial, Finset.prod_const_one]
    have hs : (∑ i ∈ β.support, Finsupp.single i (β i)) = β := Finsupp.sum_single β
    rw [hs, coeff_monomial]
    simp only [(Finsupp.mapDomain_injective hj).eq_iff, eq_comm]
  · push_neg at h
    obtain ⟨t, ht, hdt⟩ := h
    have hne : d ≠ α.mapDomain j := by
      intro hd
      have : d ∈ Set.range (Finsupp.mapDomain j) := ⟨α, hd.symm⟩
      exact hdt (((Finsupp.mem_range_mapDomain_iff j hj d).mp this) t ht)
    rw [if_neg hne, Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hdt)
      (by rw [h0 t ht, zero_pow hdt]), map_zero]

theorem coeff_subst_of_embedding {σ τ R : Type} [CommRing R] [Finite τ] (j : σ → τ)
    (hj : Function.Injective j)
    (a : τ → MvPowerSeries σ R) (ha : ∀ s, a (j s) = X s) (h0 : ∀ t, t ∉ Set.range j → a t = 0)
    (g : MvPowerSeries τ R) (α : σ →₀ ℕ) :
    coeff α (subst a g) = coeff (α.mapDomain j) g := by
  classical
  have hsub : HasSubst a := hasSubst_of_constantCoeff_zero (fun t => by
    by_cases ht : t ∈ Set.range j
    · obtain ⟨s, rfl⟩ := ht
      rw [ha]; exact constantCoeff_X s
    · rw [h0 t ht]; exact map_zero _)
  rw [coeff_subst hsub, finsum_eq_single _ (α.mapDomain j)]
  · rw [coeff_prod_pow_of_embedding j hj a ha h0, if_pos rfl, smul_eq_mul, mul_one]
  · intro d hd
    rw [coeff_prod_pow_of_embedding j hj a ha h0, if_neg hd, smul_zero]

theorem coeff_subst_restrict_sum {R ι κ : Type} [CommRing R] [Fintype ι] [Fintype κ]
    (g : MvPowerSeries (ι ⊕ κ) R) :
    (∀ α : ι →₀ ℕ, coeff α (subst (Sum.elim (fun i => (X i : MvPowerSeries ι R)) (fun _ => 0)) g) =
      coeff (α.mapDomain Sum.inl) g) ∧
    (∀ α : κ →₀ ℕ, coeff α (subst (Sum.elim (fun _ => 0) (fun i => (X i : MvPowerSeries κ R))) g) =
      coeff (α.mapDomain Sum.inr) g) := by
  refine ⟨fun α => coeff_subst_of_embedding Sum.inl Sum.inl_injective _ (fun _ => rfl) ?_ g α,
    fun α => coeff_subst_of_embedding Sum.inr Sum.inr_injective _ (fun _ => rfl) ?_ g α⟩
  · rintro (i | k) h
    · exact absurd ⟨i, rfl⟩ h
    · rfl
  · rintro (i | k) h
    · rfl
    · exact absurd ⟨k, rfl⟩ h

end GlobalTheory
