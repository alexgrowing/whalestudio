import Mathlib

open MvPolynomial Filter Topology

private noncomputable def l1 {ι : Type} (p : MvPolynomial ι ℂ) : ℝ :=
  ∑ α ∈ p.support, ‖p.coeff α‖

private theorem matrixEntryAbsSum_unitaryLie_coordinates_split {ι : Type} (p : MvPolynomial ι ℂ) (s : Finset (ι →₀ ℕ))
    (h : p.support ⊆ s) : l1 p = ∑ α ∈ s, ‖p.coeff α‖ := by
  unfold l1
  refine Finset.sum_subset h ?_
  intro x _ hx
  rw [notMem_support_iff.mp hx, norm_zero]

private theorem intMvPolynomialCoeffAbsSum_add_le {ι : Type} (p q : MvPolynomial ι ℂ) : l1 (p + q) ≤ l1 p + l1 q := by
  classical
  rw [matrixEntryAbsSum_unitaryLie_coordinates_split (p + q) (p.support ∪ q.support) support_add,
    matrixEntryAbsSum_unitaryLie_coordinates_split p (p.support ∪ q.support) Finset.subset_union_left,
    matrixEntryAbsSum_unitaryLie_coordinates_split q (p.support ∪ q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun α _ => ?_
  rw [coeff_add]
  exact norm_add_le _ _

private theorem intMvPolynomialCoeffAbsSum_sum_le {ι κ : Type} (s : Finset κ) (f : κ → MvPolynomial ι ℂ) :
    l1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, l1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l1]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (intMvPolynomialCoeffAbsSum_add_le _ _).trans (by linarith)

private theorem intMvPolynomialCoeffAbsSum_monomial {ι : Type} (a : ι →₀ ℕ) (c : ℂ) :
    l1 (monomial a c : MvPolynomial ι ℂ) = ‖c‖ := by
  classical
  rw [matrixEntryAbsSum_unitaryLie_coordinates_split _ {a} support_monomial_subset]
  simp

private theorem intMvPolynomialCoeffAbsSum_mul_le {ι : Type} (p q : MvPolynomial ι ℂ) : l1 (p * q) ≤ l1 p * l1 q := by
  have h : p * q = ∑ a ∈ p.support, ∑ b ∈ q.support,
      (monomial (a + b) (p.coeff a * q.coeff b) : MvPolynomial ι ℂ) := by
    conv_lhs => rw [p.as_sum, q.as_sum, Finset.sum_mul_sum]
    simp only [monomial_mul]
  rw [h]
  refine (intMvPolynomialCoeffAbsSum_sum_le _ _).trans ?_
  conv_rhs => rw [l1, l1, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  refine (intMvPolynomialCoeffAbsSum_sum_le _ _).trans (le_of_eq ?_)
  simp only [intMvPolynomialCoeffAbsSum_monomial, norm_mul]

private theorem l1_C_mul {ι : Type} (p : MvPolynomial ι ℂ) (c : ℂ) :
    l1 (C c * p) = ‖c‖ * l1 p := by
  rw [matrixEntryAbsSum_unitaryLie_coordinates_split (C c * p) p.support, l1, Finset.mul_sum]
  · simp only [coeff_C_mul, norm_mul]
  · intro a ha
    rw [mem_support_iff] at ha ⊢
    rw [coeff_C_mul] at ha
    exact right_ne_zero_of_mul ha

private theorem l1_homogeneousComponent_le {ι : Type} (p : MvPolynomial ι ℂ) (k : ℕ) :
    l1 (homogeneousComponent k p) ≤ l1 p := by
  rw [matrixEntryAbsSum_unitaryLie_coordinates_split (homogeneousComponent k p) p.support, l1]
  · refine Finset.sum_le_sum fun a _ => ?_
    rw [coeff_homogeneousComponent]
    split_ifs
    · exact le_rfl
    · simp
  · intro a ha
    rw [mem_support_iff] at ha ⊢
    rw [coeff_homogeneousComponent] at ha
    intro h
    apply ha
    split_ifs
    · exact h
    · rfl

private theorem l1_rename {ι ι' : Type} (p : MvPolynomial ι ℂ) (δ : ι → ι') :
    l1 (rename δ p) ≤ l1 p := by
  have h : rename δ p = ∑ a ∈ p.support,
      (monomial (Finsupp.mapDomain δ a) (p.coeff a) : MvPolynomial ι' ℂ) := by
    conv_lhs => rw [p.as_sum, map_sum]
    simp only [rename_monomial]
  rw [h]
  refine (intMvPolynomialCoeffAbsSum_sum_le _ _).trans (le_of_eq ?_)
  simp only [intMvPolynomialCoeffAbsSum_monomial]
  rfl

theorem UpperTheory.ConvolutionTheory.FX.coeffL1_submultiplicative_facts :
    ∀ (ι : Type) (p q : MvPolynomial ι ℂ), (∑ α ∈ (p + q).support, ‖(p + q).coeff α‖) ≤ (∑ α ∈ (p).support, ‖(p).coeff α‖) + (∑ α ∈ (q).support, ‖(q).coeff α‖) ∧ (∑ α ∈ (p * q).support, ‖(p * q).coeff α‖) ≤ (∑ α ∈ (p).support, ‖(p).coeff α‖) * (∑ α ∈ (q).support, ‖(q).coeff α‖) ∧ (∀ c : ℂ, (∑ α ∈ (C c * p).support, ‖(C c * p).coeff α‖) = ‖c‖ * (∑ α ∈ (p).support, ‖(p).coeff α‖)) ∧ (∀ (α₀ : ι →₀ ℕ) (c : ℂ), (∑ α ∈ ((monomial α₀ c : MvPolynomial ι ℂ)).support, ‖((monomial α₀ c : MvPolynomial ι ℂ)).coeff α‖) = ‖c‖) ∧ (∀ k, (∑ α ∈ (homogeneousComponent k p).support, ‖(homogeneousComponent k p).coeff α‖) ≤ (∑ α ∈ (p).support, ‖(p).coeff α‖)) ∧ ∀ (ι' : Type) (δ : ι → ι'), (∑ α ∈ (rename δ p).support, ‖(rename δ p).coeff α‖) ≤ (∑ α ∈ (p).support, ‖(p).coeff α‖) := by
  intro ι p q
  exact ⟨intMvPolynomialCoeffAbsSum_add_le p q, intMvPolynomialCoeffAbsSum_mul_le p q, l1_C_mul p, fun a c => intMvPolynomialCoeffAbsSum_monomial a c, l1_homogeneousComponent_le p,
    fun _ δ => l1_rename p δ⟩
