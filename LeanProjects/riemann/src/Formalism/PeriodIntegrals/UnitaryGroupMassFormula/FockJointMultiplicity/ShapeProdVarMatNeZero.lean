import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.JointMultOfSteps

noncomputable section

open Matrix FockH1Action

namespace PI.FJMD

open PI.FJM

theorem det_mem_subalgebra {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A)
    {n : ℕ} (M : Matrix (Fin n) (Fin n) A) (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply]
  refine sum_mem fun τ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (prod_mem fun i _ => h _ _) _

theorem shapeProd_mem {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A)
    {m k : ℕ} (M : Matrix (Fin m) (Fin k) A) (α : List ℕ)
    (h : ∀ (i : Fin m) (j : Fin k), i.val < α.length → j.val < α.length → M i j ∈ S) :
    shapeProd M α ∈ S := by
  unfold PI.FJM.shapeProd
  refine prod_mem fun t ht => pow_mem ?_ _
  have ht' : t < α.length := Finset.mem_range.mp ht
  unfold PI.FJM.leadT
  split_ifs with hc
  · apply det_mem_subalgebra S
    intro i j
    have hi := i.isLt
    have hj := j.isLt
    rw [Matrix.submatrix_apply]
    exact h _ _ (show i.val < α.length by omega) (show j.val < α.length by omega)
  · exact zero_mem _

theorem det_vars_ne_zero {σ : Type*} {n : ℕ} (f : Fin n × Fin n → σ) (hf : Function.Injective f) :
    (Matrix.of fun i j => (MvPolynomial.X (f (i, j)) : MvPolynomial σ ℂ)).det ≠ 0 := by
  classical
  intro h0
  have hg : ∀ i j, (if ∃ i', f (i', i') = f (i, j) then (1 : ℂ) else 0) =
      if i = j then 1 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [if_pos ⟨i, rfl⟩, if_pos rfl]
    · rw [if_neg hij, if_neg]
      rintro ⟨i', hi'⟩
      have hpair := hf hi'
      simp only [Prod.mk.injEq] at hpair
      exact hij (hpair.1.symm.trans hpair.2)
  have hmap : (MvPolynomial.eval (fun x : σ => if ∃ i', f (i', i') = x then (1 : ℂ) else 0)).mapMatrix
      (Matrix.of fun i j => (MvPolynomial.X (f (i, j)) : MvPolynomial σ ℂ)) = 1 := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.eval_X,
      Matrix.one_apply]
    exact hg i j
  have hdet := RingHom.map_det (MvPolynomial.eval (fun x : σ => if ∃ i', f (i', i') = x then (1 : ℂ) else 0))
    (Matrix.of fun i j => (MvPolynomial.X (f (i, j)) : MvPolynomial σ ℂ))
  rw [h0, map_zero, hmap, Matrix.det_one] at hdet
  exact zero_ne_one hdet

theorem shapeProd_varMat_ne_zero {p q r s m k : ℕ} (ρ : Fin m → Ix p q) (κ : Fin k → Ix r s)
    (hρ : Function.Injective ρ) (hκ : Function.Injective κ) (α : List ℕ)
    (hm : α.length ≤ m) (hk : α.length ≤ k) : shapeProd (varMat (r := r) (s := s) ρ κ) α ≠ 0 := by
  unfold PI.FJM.shapeProd
  rw [Finset.prod_ne_zero_iff]
  intro t ht
  have ht' : t < α.length := Finset.mem_range.mp ht
  apply pow_ne_zero
  have hc : t + 1 ≤ m ∧ t + 1 ≤ k := ⟨by omega, by omega⟩
  unfold PI.FJM.leadT
  rw [dif_pos hc]
  have hinj : Function.Injective
      (fun x : Fin (t + 1) × Fin (t + 1) => (ρ (Fin.castLE hc.1 x.1), κ (Fin.castLE hc.2 x.2))) := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hxy
    simp only [Prod.mk.injEq] at hxy ⊢
    exact ⟨Fin.castLE_injective _ (hρ hxy.1), Fin.castLE_injective _ (hκ hxy.2)⟩
  exact det_vars_ne_zero
    (fun x : Fin (t + 1) × Fin (t + 1) => (ρ (Fin.castLE hc.1 x.1), κ (Fin.castLE hc.2 x.2))) hinj

private theorem pderiv_pderiv_comm_of_complex {σ : Type*} (i j : σ) (P : MvPolynomial σ ℂ) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j P) = MvPolynomial.pderiv j (MvPolynomial.pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on
  next a =>
    simp only [MvPolynomial.pderiv_C, map_zero]
  next P Q hP hQ =>
    simp only [map_add, hP, hQ]
  next P n hP =>
    simp only [Derivation.leibniz, map_add, smul_eq_mul, MvPolynomial.pderiv_X, Pi.single_apply]
    split_ifs <;>
      simp only [Derivation.map_one_eq_zero, map_zero, mul_zero, zero_mul, add_zero, zero_add,
        mul_one, one_mul, hP] <;> ring

private theorem pderiv_eq_zero_of_mem_supported_of_not_mem {σ : Type*} {S : Set σ} {P : MvPolynomial σ ℂ}
    (hP : P ∈ MvPolynomial.supported ℂ S) {i : σ} (hi : i ∉ S) : MvPolynomial.pderiv i P = 0 := by
  have hv : i ∉ P.vars := fun hmem => hi ((MvPolynomial.mem_supported.mp hP) (Finset.mem_coe.mpr hmem))
  first
  | exact MvPolynomial.pderiv_eq_zero_of_notMem_vars hv
  | exact MvPolynomial.pderiv_eq_zero_of_not_mem_vars hv

theorem dd_eq_zero {p q r s : ℕ} {S : Set (Ln p q r s)} {P : Pol p q r s}
    (hP : P ∈ MvPolynomial.supported ℂ S) {l l' : Ln p q r s} (h : l ∉ S ∨ l' ∉ S) : dd l l' P = 0 := by
  have key : PI.FJM.dd l l' P = MvPolynomial.pderiv l (MvPolynomial.pderiv l' P) := by
    first
    | rfl
    | simp [PI.FJM.dd]
  rw [key]
  rcases h with h | h
  · rw [pderiv_pderiv_comm_of_complex, pderiv_eq_zero_of_mem_supported_of_not_mem hP h, map_zero]
  · rw [pderiv_eq_zero_of_mem_supported_of_not_mem hP h, map_zero]

def inS {p q r s : ℕ} (la lb lc ld : ℕ) : Ln p q r s → Prop
  | (Sum.inl i, Sum.inl k) => i.val < la ∧ k.val < la
  | (Sum.inl i, Sum.inr l) => p ≤ i.val + lb ∧ s ≤ l.val + lb
  | (Sum.inr j, Sum.inr l) => j.val < lc ∧ l.val < lc
  | (Sum.inr j, Sum.inl k) => q ≤ j.val + ld ∧ r ≤ k.val + ld

theorem posPart_length (a : List ℤ) : (PI.FJM.posPart a).length = a.length := by
  simp [PI.FJM.posPart]

theorem negPart_length (b : List ℤ) : (PI.FJM.negPart b).length = b.length := by
  simp [PI.FJM.negPart]

private theorem fin_rev_val {n : ℕ} (i : Fin n) : (Fin.rev i).val = n - (i.val + 1) := rfl

private theorem varMat_apply_mem_supported {p q r s m k : ℕ} (ρ : Fin m → FockH1Action.Ix p q)
    (κ : Fin k → FockH1Action.Ix r s) (T : Set (FockH1Action.Ln p q r s)) (i : Fin m) (j : Fin k)
    (h : (ρ i, κ j) ∈ T) : PI.FJM.varMat ρ κ i j ∈ MvPolynomial.supported ℂ T := by
  rw [show PI.FJM.varMat ρ κ i j = MvPolynomial.X (ρ i, κ j) from rfl]
  first
  | exact MvPolynomial.X_mem_supported.mpr h
  | exact MvPolynomial.mem_supported.mpr (by rw [MvPolynomial.vars_X]; simpa using h)

theorem hwVec_mem_supported (p q r s : ℕ) (a b c d : List ℤ) :
    hwVec p q r s a b c d ∈ MvPolynomial.supported ℂ
      {l : Ln p q r s | inS a.length b.length c.length d.length l} := by
  unfold PI.FJM.hwVec
  refine mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_
  · apply shapeProd_mem
    intro i j hi hj
    rw [posPart_length] at hi hj
    apply varMat_apply_mem_supported
    simp only [Set.mem_setOf_eq, inS]
    exact ⟨hi, hj⟩
  · apply shapeProd_mem
    intro i j hi hj
    rw [negPart_length] at hi hj
    apply varMat_apply_mem_supported
    simp only [Set.mem_setOf_eq, inS, fin_rev_val]
    have := i.isLt
    have := j.isLt
    constructor <;> omega
  · apply shapeProd_mem
    intro i j hi hj
    rw [posPart_length] at hi hj
    apply varMat_apply_mem_supported
    simp only [Set.mem_setOf_eq, inS]
    exact ⟨hi, hj⟩
  · apply shapeProd_mem
    intro i j hi hj
    rw [negPart_length] at hi hj
    apply varMat_apply_mem_supported
    simp only [Set.mem_setOf_eq, inS, fin_rev_val]
    have := i.isLt
    have := j.isLt
    constructor <;> omega

theorem shapeVector_ne_zero : VecNe := by
  intro p q r s a b c d h
  obtain ⟨-, -, -, -, -, -, -, -, h1, h2, h3, h4⟩ := h
  unfold PI.FJM.hwVec
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_
  · exact shapeProd_varMat_ne_zero _ _
      (by intro x y hxy; exact Sum.inl_injective hxy) (by intro x y hxy; exact Sum.inl_injective hxy) _
      (by rw [posPart_length]; omega) (by rw [posPart_length]; omega)
  · exact shapeProd_varMat_ne_zero _ _
      (by intro x y hxy; exact Fin.rev_injective (Sum.inl_injective hxy))
      (by intro x y hxy; exact Fin.rev_injective (Sum.inr_injective hxy)) _
      (by rw [negPart_length]; omega) (by rw [negPart_length]; omega)
  · exact shapeProd_varMat_ne_zero _ _
      (by intro x y hxy; exact Sum.inr_injective hxy) (by intro x y hxy; exact Sum.inr_injective hxy) _
      (by rw [posPart_length]; omega) (by rw [posPart_length]; omega)
  · exact shapeProd_varMat_ne_zero _ _
      (by intro x y hxy; exact Fin.rev_injective (Sum.inr_injective hxy))
      (by intro x y hxy; exact Fin.rev_injective (Sum.inl_injective hxy)) _
      (by rw [negPart_length]; omega) (by rw [negPart_length]; omega)

private theorem moduleEnd_finset_sum_apply {V : Type*} [AddCommGroup V] [Module ℂ V] {ι : Type*}
    (t : Finset ι) (f : ι → Module.End ℂ V) (v : V) : (∑ x ∈ t, f x) v = ∑ x ∈ t, f x v := by
  first
  | exact LinearMap.sum_apply t f v
  | simp

theorem vecJ_of (hF : FormJ) : VecJ := by
  intro p q r s a b c d h
  have hsupp := hwVec_mem_supported p q r s a b c d
  obtain ⟨-, -, -, -, -, -, -, -, h1, h2, h3, h4⟩ := h
  refine (hF p q r s (PI.FJM.hwVec p q r s a b c d)).mpr ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    unfold PI.FJM.lapA
    rw [moduleEnd_finset_sum_apply]
    refine Finset.sum_eq_zero fun l _ => dd_eq_zero hsupp ?_
    refine not_and_or.mp ?_
    rintro ⟨hx, hy⟩
    simp only [Set.mem_setOf_eq, inS] at hx hy
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    omega
  · intro i j
    unfold PI.FJM.lapB
    rw [moduleEnd_finset_sum_apply]
    refine Finset.sum_eq_zero fun k _ => dd_eq_zero hsupp ?_
    refine not_and_or.mp ?_
    rintro ⟨hx, hy⟩
    simp only [Set.mem_setOf_eq, inS] at hx hy
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    omega
  · intro k l
    unfold PI.FJM.lapC
    rw [moduleEnd_finset_sum_apply]
    refine Finset.sum_eq_zero fun i _ => dd_eq_zero hsupp ?_
    refine not_and_or.mp ?_
    rintro ⟨hx, hy⟩
    simp only [Set.mem_setOf_eq, inS] at hx hy
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    omega
  · intro k l
    unfold PI.FJM.lapD
    rw [moduleEnd_finset_sum_apply]
    refine Finset.sum_eq_zero fun j _ => dd_eq_zero hsupp ?_
    refine not_and_or.mp ?_
    rintro ⟨hx, hy⟩
    simp only [Set.mem_setOf_eq, inS] at hx hy
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    omega

end PI.FJMD
