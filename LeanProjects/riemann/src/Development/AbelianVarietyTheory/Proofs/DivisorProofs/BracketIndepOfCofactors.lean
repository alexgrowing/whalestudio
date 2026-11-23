import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KoszulSyzygyAntisymmetricCoefficientsStatement
open MvPolynomial Finset

namespace GlobalTheory

theorem bracket_indep_of_cofactors : ∀ (A B M : Type) [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] (r : ℕ) (D : Fin r → B) (m : Fin r → M),
    (∀ i j, D j • m i = D i • m j) → ∀ G G' : Fin r → MvPolynomial (Fin r) A,
    ∑ i, X i * G i = ∑ i, X i * G' i →
    ∑ i, aeval D (G i) • m i = ∑ i, aeval D (G' i) • m i := by
  intro A B M _ _ _ _ _ r D m hDm G G' hGG'
  have h0 : ∑ i, X i * (fun i => G i - G' i) i = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, hGG', sub_self]
  obtain ⟨H, hanti, hdiag, hG⟩ := GlobalTheory.T.koszul_syzygy_antisymmetric_coefficients A r (fun i => G i - G' i) h0
  have hG' : ∀ i, G i - G' i = ∑ j, X j * H i j := hG
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  have hterm : ∀ i, aeval D (G i) • m i - aeval D (G' i) • m i
      = ∑ j, aeval D (H i j) • (D j • m i) := by
    intro i
    rw [← sub_smul, ← map_sub, hG' i, map_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, aeval_X, mul_comm, mul_smul]
  simp_rw [hterm]
  rw [← Finset.sum_product' (s := (univ : Finset (Fin r))) (t := univ)
    (f := fun i j => aeval D (H i j) • (D j • m i))]
  refine Finset.sum_involution (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ _
    simp only
    rw [hanti j i, map_neg, neg_smul, (hDm i j).symm, add_neg_cancel]
  · rintro ⟨i, j⟩ _ hne heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, -⟩ := heq
    exact hne (by simp only [hdiag, map_zero, zero_smul])
  · intro p _
    simp
  · intro p _
    rfl

end GlobalTheory
