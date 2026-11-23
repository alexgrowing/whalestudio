import Mathlib

open MvPolynomial

noncomputable section

namespace PI.FJMX

section Deriv

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

theorem deriv_prod_eq_zero {ι : Type*} (D : Derivation R A A) (s : Finset ι) (f : ι → A)
    (h : ∀ i ∈ s, D (f i) = 0) : D (∏ i ∈ s, f i) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, D.leibniz, h a (Finset.mem_insert_self a s),
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi))]
    simp

theorem deriv_pow_eq_zero (D : Derivation R A A) (a : A) (n : ℕ) (h : D a = 0) :
    D (a ^ n) = 0 := by
  rw [D.leibniz_pow, h]; simp

theorem deriv_finset_prod {ι : Type*} [DecidableEq ι] (D : Derivation R A A) (s : Finset ι)
    (f : ι → A) : D (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * D (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, D.leibniz, ih, Finset.sum_insert ha, Finset.erase_insert ha]
    simp only [smul_eq_mul]
    rw [add_comm, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hne : i ≠ a := fun h => ha (h ▸ hi)
    rw [Finset.erase_insert_of_ne hne.symm, Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
    ring

theorem deriv_det {n : Type*} [Fintype n] [DecidableEq n] (D : Derivation R A A)
    (M : Matrix n n A) :
    D M.det = ∑ i, (M.updateCol i (fun k => D (M k i))).det := by
  simp only [Matrix.det_apply, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Units.smul_def, map_zsmul, deriv_finset_prod, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Units.smul_def]
  congr 1
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  congr 1
  · apply Finset.prod_congr rfl
    intro j hj
    rw [Matrix.updateCol_ne (Finset.ne_of_mem_erase hj)]
  · rw [Matrix.updateCol_self]

theorem deriv_det_eq_zero {n : Type*} [Fintype n] [DecidableEq n] (D : Derivation R A A)
    (M : Matrix n n A)
    (h : ∀ i, (∀ k, D (M k i) = 0) ∨ ∃ i', i' ≠ i ∧ ∃ c : A, ∀ k, D (M k i) = c * M k i') :
    D M.det = 0 := by
  rw [deriv_det]
  apply Finset.sum_eq_zero
  intro i _
  rcases h i with h0 | ⟨i', hne, c, hc⟩
  · have : (fun k => D (M k i)) = 0 := funext h0
    rw [this]
    simpa using Matrix.det_updateCol_smul M i (0 : A) 0
  · have : (fun k => D (M k i)) = c • (fun k => M k i') := funext fun k => by simp [hc k]
    rw [this, Matrix.det_updateCol_smul]
    rw [Matrix.det_zero_of_column_eq hne.symm]
    · simp
    · intro k
      simp [Matrix.updateCol_self, Matrix.updateCol_ne hne]

theorem deriv_det_eq_zero_rows {n : Type*} [Fintype n] [DecidableEq n] (D : Derivation R A A)
    (M : Matrix n n A)
    (h : ∀ i, (∀ k, D (M i k) = 0) ∨ ∃ i', i' ≠ i ∧ ∃ c : A, ∀ k, D (M i k) = c * M i' k) :
    D M.det = 0 := by
  rw [← Matrix.det_transpose]
  exact deriv_det_eq_zero D M.transpose h

end Deriv

section Minor

variable {R : Type*} [CommRing R] {σ : Type*}

def minorPolynomial (R : Type*) [CommRing R] {k : ℕ} (g : Fin k → Fin k → σ) : MvPolynomial σ R :=
  (Matrix.of fun i j => (X (g i j) : MvPolynomial σ R)).det

theorem minorPolynomial_ne_zero [IsDomain R] {k : ℕ} (g : Fin k → Fin k → σ)
    (hg : Function.Injective (fun x : Fin k × Fin k => g x.1 x.2)) : minorPolynomial R g ≠ 0 := by
  have e : minorPolynomial R g = rename (fun x : Fin k × Fin k => g x.1 x.2)
      (Matrix.mvPolynomialX (Fin k) (Fin k) R).det := by
    rw [AlgHom.map_det, minorPolynomial]
    congr 1
    ext i j
    simp [Matrix.mvPolynomialX]
  rw [e]
  intro h
  apply Matrix.det_mvPolynomialX_ne_zero (m := Fin k) (R := R)
  exact (rename_injective _ hg) (by rw [h, map_zero])

theorem minorPolynomial_isWeightedHomogeneous {k : ℕ} (g : Fin k → Fin k → σ) (w : σ → ℕ) (u v : Fin k → ℕ)
    (hw : ∀ i j, w (g i j) = u i + v j) :
    IsWeightedHomogeneous w (minorPolynomial R g) (∑ i, u i + ∑ j, v j) := by
  classical
  rw [minorPolynomial, Matrix.det_apply']
  apply IsWeightedHomogeneous.sum
  intro τ _
  have hp : IsWeightedHomogeneous w
      (∏ i, (Matrix.of fun i j => (X (g i j) : MvPolynomial σ R)) (τ i) i)
      (∑ i, w (g (τ i) i)) :=
    IsWeightedHomogeneous.prod _ _ _ fun i _ => isWeightedHomogeneous_X _ _ _
  have hc : ∑ i, w (g (τ i) i) = ∑ i, u i + ∑ j, v j := by
    simp only [hw, Finset.sum_add_distrib]
    congr 1
    exact Equiv.sum_comp τ u
  rw [hc] at hp
  have h0 : IsWeightedHomogeneous w (((Equiv.Perm.sign τ : ℤ) : MvPolynomial σ R)) 0 := by
    rw [← map_intCast (C : R →+* MvPolynomial σ R)]
    exact isWeightedHomogeneous_C _ _
  have := h0.mul hp
  rw [zero_add] at this
  exact this

theorem minorPolynomial_mem_supported {k : ℕ} (g : Fin k → Fin k → σ) (S : Set σ) (hS : ∀ i j, g i j ∈ S) :
    minorPolynomial R g ∈ supported R S := by
  classical
  rw [minorPolynomial, Matrix.det_apply']
  apply Subalgebra.sum_mem
  intro τ _
  apply Subalgebra.mul_mem
  · exact Subalgebra.intCast_mem _ _
  · apply Subalgebra.prod_mem
    intro i _
    simp only [Matrix.of_apply]
    exact Algebra.subset_adjoin ⟨g (τ i) i, hS _ _, rfl⟩

theorem pderiv_eq_zero_of_supported {S : Set σ} {f : MvPolynomial σ R} (hf : f ∈ supported R S)
    {v : σ} (hv : v ∉ S) : pderiv v f = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro h
  exact hv ((mem_supported.1 hf) h)

theorem pderiv_mem_supported {S : Set σ} {f : MvPolynomial σ R} (hf : f ∈ supported R S)
    (v : σ) : pderiv v f ∈ supported R S := by
  classical
  by_cases hv : v ∈ S
  · rw [supported_eq_range_rename] at hf ⊢
    obtain ⟨g, rfl⟩ := hf
    have := pderiv_rename (R := R) Subtype.val_injective (⟨v, hv⟩ : S) g
    simp only at this
    change pderiv v (rename Subtype.val g) ∈ _
    rw [this]
    exact AlgHom.mem_range_self _ _
  · rw [pderiv_eq_zero_of_supported hf hv]
    exact Subalgebra.zero_mem _

end Minor

end PI.FJMX
