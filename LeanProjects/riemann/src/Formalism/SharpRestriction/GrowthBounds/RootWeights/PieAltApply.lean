import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def pie_cnt {n b : ℕ} (s : Sym (Fin n) b) : Fin n → ℕ := fun i => (s : Multiset (Fin n)).count i

theorem pie_hsymm (n b : ℕ) : hsymm (Fin n) ℤ b =
    ∑ s : Sym (Fin n) b, ∏ i, (X i : MvPolynomial (Fin n) ℤ) ^ pie_cnt s i := by
  rw [MvPolynomial.hsymm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.prod_multiset_map_count]
  simp only [pie_cnt]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  rw [Multiset.mem_toFinset] at hi
  rw [Multiset.count_eq_zero.mpr hi, pow_zero]

theorem pie_alt_apply (n : ℕ) (al : Fin n → ℕ) : alt n al =
    ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, (X (σ i) : MvPolynomial (Fin n) ℤ) ^ al i := by
  unfold alt
  rw [Matrix.det_apply]
  rfl

private theorem pie_cnt_map_equiv {n b : ℕ} (e : Fin n ≃ Fin n) (s : Sym (Fin n) b) (i : Fin n) :
    pie_cnt (s.map e) i = pie_cnt s (e.symm i) := by
  unfold pie_cnt
  rw [Sym.coe_map]
  conv_lhs => rw [← e.apply_symm_apply i]
  exact Multiset.count_map_eq_count' e _ e.injective _

theorem pie_step1 (n b : ℕ) (al : Fin n → ℕ) : alt n al * hsymm (Fin n) ℤ b =
    ∑ s : Sym (Fin n) b, alt n (al + pie_cnt s) := by
  rw [pie_alt_apply, pie_hsymm, Finset.sum_mul]
  simp_rw [pie_alt_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  rw [smul_mul_assoc, Finset.mul_sum, ← Finset.smul_sum]
  congr 1
  refine Finset.sum_nbij' (fun s => s.map σ.symm) (fun s => s.map σ) (by simp) (by simp) ?_ ?_ ?_
  · intro s _
    first
    | simp [Sym.map_map]
    | (apply Sym.ext; simp [Sym.coe_map, Multiset.map_map])
  · intro s _
    first
    | simp [Sym.map_map]
    | (apply Sym.ext; simp [Sym.coe_map, Multiset.map_map])
  · intro s _
    rw [← Equiv.prod_comp σ (fun i => (X i : MvPolynomial (Fin n) ℤ) ^ pie_cnt s i),
      ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [Pi.add_apply, pow_add, pie_cnt_map_equiv, Equiv.symm_symm]

end Formalism.MainNotions.G.GLWeightTheory
