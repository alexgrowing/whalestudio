import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasisApply
open NumberField
open scoped TensorProduct

namespace GlobalTheory.UnitaryStd

variable {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) (g : ℕ)

theorem form_cx_coord (S : Matrix (Fin r) (Fin r) ℤ) (y z : Lat ρ g) :
    form ρ g S (cx ρ g y) z = ∑ i, ∑ j, S i j *
      ∑ α : Fin g ⊕ Fin g, (basis ρ g).repr y (i, α) * (basis ρ g).repr z (j, α) := by
  rw [form_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [cx_apply, basis_repr, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, dotProduct,
    Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, sub_neg_eq_add]
  ring

theorem form_cx_basis (S : Matrix (Fin r) (Fin r) ℤ) (p q : Fin r × (Fin g ⊕ Fin g)) :
    form ρ g S (cx ρ g (basis ρ g p)) (basis ρ g q) = if p.2 = q.2 then S p.1 q.1 else 0 := by
  rw [form_cx_coord]
  obtain ⟨i0, a⟩ := p
  obtain ⟨j0, b⟩ := q
  simp only [Module.Basis.repr_self, Finsupp.single_apply, Prod.mk.injEq]
  simp [ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]

theorem form_cx_baseChange_pos (S : Matrix (Fin r) (Fin r) ℤ) (hS : (S.map (Int.cast : ℤ → ℝ)).PosDef)
    (x : ℝ ⊗[ℤ] Lat ρ g) (hx : x ≠ 0) :
    0 < (form ρ g S).baseChange ℝ ((cx ρ g).baseChange ℝ x) x := by
  set b := Algebra.TensorProduct.basis ℝ (basis ρ g) with hb
  set c := b.repr x with hc
  have hx' : x = ∑ p, c p • b p := (b.sum_repr x).symm
  have key : (form ρ g S).baseChange ℝ ((cx ρ g).baseChange ℝ x) x =
      ∑ q, ∑ p, c p * c q * (((if p.2 = q.2 then S p.1 q.1 else 0 : ℤ)) : ℝ) := by
    conv_lhs => rw [hx']
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hb,
      Algebra.TensorProduct.basis_apply, LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul,
      form_cx_basis, mul_one, zsmul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    ring
  set v : (Fin g ⊕ Fin g) → Fin r → ℝ := fun α i => c (i, α) with hv
  have key2 : (form ρ g S).baseChange ℝ ((cx ρ g).baseChange ℝ x) x =
      ∑ α, v α ⬝ᵥ ((S.map (Int.cast : ℤ → ℝ)).mulVec (v α)) := by
    rw [key, Finset.sum_comm]
    simp only [Fintype.sum_prod_type, Int.cast_ite, Int.cast_zero, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, dotProduct, Matrix.mulVec,
      Matrix.map_apply, Finset.mul_sum, hv]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [key2]
  have hnn : ∀ α, 0 ≤ v α ⬝ᵥ ((S.map (Int.cast : ℤ → ℝ)).mulVec (v α)) := by
    intro α
    by_cases h0 : v α = 0
    · simp [h0]
    · simpa using (hS.dotProduct_mulVec_pos h0).le
  have hne : c ≠ 0 := by
    intro h; apply hx; rw [hx']; simp [h]
  obtain ⟨⟨i, α⟩, hp⟩ : ∃ p, c p ≠ 0 := by
    by_contra h; push_neg at h; exact hne (Finsupp.ext h)
  have hα : v α ≠ 0 := fun h => hp (by simpa [hv] using congrFun h i)
  have hpos : 0 < v α ⬝ᵥ ((S.map (Int.cast : ℤ → ℝ)).mulVec (v α)) := by
    simpa using hS.dotProduct_mulVec_pos hα
  exact lt_of_lt_of_le hpos (Finset.single_le_sum (fun β _ => hnn β) (Finset.mem_univ α))

end GlobalTheory.UnitaryStd
