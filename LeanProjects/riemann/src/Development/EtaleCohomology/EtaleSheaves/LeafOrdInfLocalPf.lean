import Development.EtaleCohomology.EtaleSheaves.LeafOrdInfHomPf

namespace LateralTheory.E.E4

open Polynomial

def LeafFinInf : Prop := ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B] (g : Polynomial k →ₐ[k] B), Function.Injective g → g.Finite →
  Transcendental k (algebraMap B (FractionRing B) (g Polynomial.X))⁻¹ ∧
  FiniteDimensional (IntermediateField.adjoin k {(algebraMap B (FractionRing B) (g Polynomial.X))⁻¹}) (FractionRing B)

def LeafFinVal : Prop := ∀ (k L : Type) [Field k] [IsAlgClosed k] [Field L] [Algebra k L] (s : L), Transcendental k s →
  FiniteDimensional (IntermediateField.adjoin k {s}) L →
  ∃ (n : ℕ) (φ : Lˣ →* Multiplicative (Fin n → ℤ)), ∀ x : Lˣ, φ x = 1 →
    ∃ (d : ℕ) (a b : ℕ → Polynomial k), (∀ i, (b i).eval 0 ≠ 0) ∧
      (x : L) ^ d + ∑ i ∈ Finset.range d, (aeval s (a i) / aeval s (b i)) * (x : L) ^ i = 0

def LeafClearDen : Prop := ∀ (k L : Type) [Field k] [Field L] [Algebra k L] (s : L), Transcendental k s →
  ∀ (x : L) (d : ℕ) (a b : ℕ → Polynomial k), (∀ i, (b i).eval 0 ≠ 0) →
    x ^ d + ∑ i ∈ Finset.range d, (aeval s (a i) / aeval s (b i)) * x ^ i = 0 →
    ∃ h : Polynomial k, h.eval 0 ≠ 0 ∧ IsIntegral (Algebra.adjoin k {s, (aeval s h)⁻¹}) x

theorem LeafOrdInfLocal_of (h1 : LeafFinInf) (h2 : LeafFinVal) (h3 : LeafClearDen) : LeafOrdInfLocal := by
  intro k B _ _ _ _ _ _ g hg hf
  obtain ⟨hT, hfd⟩ := h1 k B g hg hf
  obtain ⟨n, φ, hφ⟩ := h2 k (FractionRing B) _ hT hfd
  refine ⟨n, φ.comp (Units.map (algebraMap B (FractionRing B) : B →* FractionRing B)), fun u hu => ?_⟩
  obtain ⟨d, a, b, hb, heq⟩ := hφ (Units.map (algebraMap B (FractionRing B) : B →* FractionRing B) u) hu
  exact h3 k (FractionRing B) _ hT _ d a b hb heq

theorem integral_after_clearing_polynomial_denominators_holds : LeafClearDen := by
  intro k L _ _ _ s hs x d a b hb heq
  have hne : ∀ p : Polynomial k, p ≠ 0 → aeval s p ≠ 0 := fun p hp h0 => hp ((transcendental_iff.mp hs) p h0)
  have hb0 : ∀ i, b i ≠ 0 := fun i h => hb i (by simp [h])
  set h := ∏ i ∈ Finset.range d, b i with hh
  have he : h.eval 0 ≠ 0 := by
    rw [hh, Polynomial.eval_prod]; exact Finset.prod_ne_zero_iff.mpr (fun i _ => hb i)
  refine ⟨h, he, ?_⟩
  set A := Algebra.adjoin k {s, (aeval s h)⁻¹}
  have hpol : ∀ p : Polynomial k, aeval s p ∈ A := fun p =>
    Algebra.adjoin_mono (by intro y hy; rw [Set.mem_singleton_iff.mp hy]; exact Or.inl rfl)
      (Polynomial.aeval_mem_adjoin_singleton k s)
  have hinv : (aeval s h)⁻¹ ∈ A := Algebra.subset_adjoin (Or.inr rfl)
  have hmem : ∀ i ∈ Finset.range d, aeval s (a i) / aeval s (b i) ∈ A := by
    intro i hi
    have hsplit : h = b i * ∏ j ∈ (Finset.range d).erase i, b j := (Finset.mul_prod_erase _ _ hi).symm
    have hr : aeval s (∏ j ∈ (Finset.range d).erase i, b j) ≠ 0 :=
      hne _ (Finset.prod_ne_zero_iff.mpr (fun j _ => hb0 j))
    have hbi : aeval s (b i) ≠ 0 := hne _ (hb0 i)
    have : aeval s (a i) / aeval s (b i) =
        aeval s (a i * ∏ j ∈ (Finset.range d).erase i, b j) * (aeval s h)⁻¹ := by
      rw [hsplit, map_mul, map_mul]; field_simp
    rw [this]; exact A.mul_mem (hpol _) hinv
  let c : ℕ → A := fun i => if hi : i ∈ Finset.range d then ⟨_, hmem i hi⟩ else 0
  have hdeg : (∑ i ∈ Finset.range d, C (c i) * X ^ i : A[X]).degree < (d : WithBot ℕ) := by
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
    intro i hi
    exact lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) (by exact_mod_cast Finset.mem_range.mp hi)
  refine ⟨(X ^ d + ∑ i ∈ Finset.range d, C (c i) * X ^ i : A[X]), monic_X_pow_add hdeg, ?_⟩
  rw [eval₂_add, eval₂_X_pow, eval₂_finsetSum]
  rw [← heq]
  congr 1
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : i < d := Finset.mem_range.mp hi
  rw [eval₂_mul, eval₂_C, eval₂_X_pow]
  congr 1
  simp only [c, Finset.mem_range, hi', dif_pos]
  rfl

theorem LeafOrdInfLocal_of' (h1 : LeafFinInf) (h2 : LeafFinVal) : LeafOrdInfLocal :=
  LeafOrdInfLocal_of h1 h2 integral_after_clearing_polynomial_denominators_holds

end LateralTheory.E.E4
