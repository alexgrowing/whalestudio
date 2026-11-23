import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDerivationCotangentIndependent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing Matrix

theorem derivation_mem_of_mem_sq {T : Type} [CommRing T] (P : Ideal T) (D : Derivation ℤ T T)
    {x : T} (hx : x ∈ P ^ 2) : D x ∈ P := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact P.add_mem (P.mul_mem_right _ ha) (P.mul_mem_right _ hb)
  · rw [map_add]; exact P.add_mem ha hb

theorem mem_of_derivation_det_not_mem {T : Type} [CommRing T] (P : Ideal T) [P.IsPrime] {h : ℕ}
    (D : Fin h → Derivation ℤ T T) (f : Fin h → T) (hf : ∀ i, f i ∈ P)
    (hdet : (Matrix.of fun i j => D j (f i)).det ∉ P) (b : Fin h → T) (t : T) (ht : t ∉ P)
    (hsum : t * ∑ i, b i * f i ∈ P ^ 2) (i : Fin h) : b i ∈ P := by
  set A : Matrix (Fin h) (Fin h) T := Matrix.of fun i j => D j (f i) with hA

  have hv : ∀ j, (b ᵥ* A) j ∈ P := by
    intro j
    have h1 := derivation_mem_of_mem_sq P (D j) hsum
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_sum] at h1
    have h2 : (∑ i, b i * f i) * D j t ∈ P :=
      P.mul_mem_right _ (P.sum_mem fun i _ => P.mul_mem_left _ (hf i))
    have h3 : t * ∑ i, D j (b i * f i) ∈ P := by
      have := P.sub_mem h1 h2; simpa using this
    have h4 : ∑ i, D j (b i * f i) ∈ P :=
      ((Ideal.IsPrime.mem_or_mem inferInstance h3).resolve_left ht)
    have h5 : ∑ i, D j (b i * f i) - ∑ i, f i * D j (b i) = (b ᵥ* A) j := by
      rw [← Finset.sum_sub_distrib]
      simp only [Matrix.vecMul, dotProduct, hA, Matrix.of_apply, Derivation.leibniz, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [← h5]
    exact P.sub_mem h4 (P.sum_mem fun i _ => P.mul_mem_right _ (hf i))

  have hw : (b ᵥ* A ᵥ* A.adjugate) i = A.det * b i := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul, Matrix.vecMul_one,
      Pi.smul_apply, smul_eq_mul]
  have hmem : (b ᵥ* A ᵥ* A.adjugate) i ∈ P := by
    simp only [Matrix.vecMul, dotProduct]
    exact P.sum_mem fun j _ => P.mul_mem_right _ (hv j)
  rw [hw] at hmem
  exact (Ideal.IsPrime.mem_or_mem inferInstance hmem).resolve_left hdet

theorem DerivationCotangentIndependent.proof : DerivationCotangentIndependent.Statement := by
  intro T _ P _ h D f hf hdet a hsum i

  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples P.primeCompl (Finset.univ : Finset (Fin h)) a
  choose b hb using fun k => hs k (Finset.mem_univ k)

  have hmax : maximalIdeal (Localization.AtPrime P) = P.map (algebraMap T (Localization.AtPrime P)) :=
    (Localization.AtPrime.map_eq_maximalIdeal).symm
  have hsq : algebraMap T (Localization.AtPrime P) (∑ k, b k * f k) ∈ (P ^ 2).map (algebraMap T (Localization.AtPrime P)) := by
    rw [Ideal.map_pow, ← hmax]
    have : algebraMap T (Localization.AtPrime P) (∑ k, b k * f k) =
        algebraMap T (Localization.AtPrime P) (s : T) * ∑ k, a k * algebraMap T (Localization.AtPrime P) (f k) := by
      simp only [map_sum, map_mul, Finset.mul_sum, hb, Algebra.smul_def]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [this]
    exact Ideal.mul_mem_left _ _ hsum
  obtain ⟨⟨⟨y, hy⟩, u⟩, hyu⟩ := (IsLocalization.mem_map_algebraMap_iff P.primeCompl (Localization.AtPrime P)).1 hsq
  rw [← map_mul] at hyu
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists P.primeCompl (Localization.AtPrime P)).1 hyu
  have hbi : b i ∈ P := by
    refine mem_of_derivation_det_not_mem P D f hf hdet b ((c : T) * (u : T)) ?_ ?_ i
    · exact (P.primeCompl.mul_mem c.2 u.2 : _)
    · have : (c : T) * (u : T) * ∑ k, b k * f k = (c : T) * y := by rw [← hc]; ring
      rw [this]; exact Ideal.mul_mem_left _ _ hy

  have hsa : algebraMap T (Localization.AtPrime P) (s : T) * a i ∈ maximalIdeal (Localization.AtPrime P) := by
    rw [← Algebra.smul_def, ← hb i]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P _).2 hbi
  have hs' : algebraMap T (Localization.AtPrime P) (s : T) ∉ maximalIdeal (Localization.AtPrime P) := by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P]; exact s.2
  exact ((maximalIdeal.isMaximal (Localization.AtPrime P)).isPrime.mem_or_mem hsa).resolve_left hs'

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
