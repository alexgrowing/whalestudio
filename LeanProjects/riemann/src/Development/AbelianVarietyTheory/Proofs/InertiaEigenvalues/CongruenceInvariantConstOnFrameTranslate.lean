import Mathlib
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem invariant_const_on_translate : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ (Φ : Matrix (Fin r ⊕ Fin t) (Fin r) K → ℂ), (∀ h : GL (Fin r ⊕ Fin t) O, (∀ a b, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inl a) (Sum.inl b) - (1 : Matrix (Fin r) (Fin r) O) a b ∈ Ideal.span {ϖ}) → (∀ a b, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inr a) (Sum.inl b) ∈ Ideal.span {ϖ}) → ∀ x : Matrix (Fin r ⊕ Fin t) (Fin r) K, Φ ((h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O).map (algebraMap O K) * x) = Φ x) → ∀ (x : Matrix (Fin r ⊕ Fin t) (Fin r) K) (g : GL (Fin r) K) (z : Matrix (Fin r ⊕ Fin t) (Fin r) O), x * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z).map (algebraMap O K) → Φ x = Φ ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)).map (algebraMap O K) * ((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)) := by
  intro O K _ _ _ _ _ _ _ r t ϖ hϖ Φ hΦ x g z hx
  classical
  set z₁ : Matrix (Fin r) (Fin r) O := Matrix.toRows₁ z
  set z₂ : Matrix (Fin t) (Fin r) O := Matrix.toRows₂ z
  set M : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O :=
    Matrix.fromBlocks (1 + ϖ • z₁) 0 (ϖ • z₂) 1 with hMdef
  have hmem : ϖ ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit
  have hres : IsLocalRing.residue O ϖ = 0 := (IsLocalRing.residue_eq_zero_iff ϖ).2 hmem
  have hdet : IsUnit M.det := by
    rw [hMdef, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one,
      ← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, RingHom.map_det]
    have h1 : (IsLocalRing.residue O).mapMatrix (1 + ϖ • z₁) = 1 := by
      ext i j
      simp [Matrix.one_apply, hres]
    rw [h1, Matrix.det_one]
    exact one_ne_zero
  let h : GL (Fin r ⊕ Fin t) O := M.nonsingInvUnit hdet
  have hh : (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) = M := rfl
  set e : Matrix (Fin r ⊕ Fin t) (Fin r) O :=
    Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O) with hedef
  have key : M * e = e + ϖ • z := by
    ext (a | a) b <;>
      simp [hMdef, hedef, z₁, z₂, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks,
        Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.toRows₁, Matrix.toRows₂, Matrix.one_apply, add_mul, Sum.elim_inl,
        Sum.elim_inr, mul_ite, ite_mul, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq']
  have h1 : ∀ a b, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inl a) (Sum.inl b) -
      (1 : Matrix (Fin r) (Fin r) O) a b ∈ Ideal.span {ϖ} := by
    intro a b
    rw [hh, hMdef, Matrix.fromBlocks_apply₁₁, Matrix.add_apply, add_sub_cancel_left,
      Matrix.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self ϖ)
  have h2 : ∀ a b, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inr a) (Sum.inl b) ∈
      Ideal.span {ϖ} := by
    intro a b
    rw [hh, hMdef, Matrix.fromBlocks_apply₂₁, Matrix.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self ϖ)
  have hinv := hΦ h h1 h2 (e.map (algebraMap O K) * ((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K))
  rw [← hinv, hh, ← Matrix.mul_assoc, ← Matrix.map_mul, key, ← hx, Matrix.mul_assoc,
    Units.mul_inv, Matrix.mul_one]

end GlobalTheory
