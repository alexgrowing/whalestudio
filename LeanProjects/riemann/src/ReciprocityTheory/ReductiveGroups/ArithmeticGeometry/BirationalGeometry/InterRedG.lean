import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial ReciprocityTheory.AnForm.M

section Alg

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

open Classical in
theorem blockDeg_single (q : Σ k, ι k) (m : ℕ) (k' : K) :
    ∑ i, (Finsupp.single q m : (Σ k, ι k) →₀ ℕ) ⟨k', i⟩ = if q.1 = k' then m else 0 := by
  obtain ⟨k0, i0⟩ := q
  by_cases h : k0 = k'
  · subst h
    simp [Finsupp.single_apply, Sigma.mk.inj_iff]
  · simp [Finsupp.single_apply, Sigma.mk.inj_iff, h]

def secOf (i : ∀ k, ι k) (b : K → ℕ) : MRing ι := ∏ k, X ⟨k, i k⟩ ^ b k

theorem secOf_eq (i : ∀ k, ι k) (b : K → ℕ) :
    secOf i b = monomial (∑ k, Finsupp.single (⟨k, i k⟩ : Σ k, ι k) (b k)) 1 := by
  rw [secOf, MvPolynomial.monomial_sum_one]
  simp [MvPolynomial.X_pow_eq_monomial]

theorem isMultiHomog_secOf (i : ∀ k, ι k) (b : K → ℕ) : IsMultiHomog (secOf i b) b := by
  classical
  intro m hm k
  rw [secOf_eq, MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hm
  subst hm
  simp only [Finsupp.finset_sum_apply]
  rw [Finset.sum_comm]
  simp only [blockDeg_single]
  simp

theorem secOf_not_mem {P : Ideal (MRing ι)} (hP : P.IsPrime) {i : ∀ k, ι k}
    (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι) ∉ P) (b : K → ℕ) : secOf i b ∉ P := by
  rw [secOf]
  intro h
  obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hP)).1 h
  exact hi k (hP.mem_of_pow_mem _ hk)

def eLine : HermLine ι := HermLine.ofWeight (fun _ => -1) (fun _ _ _ => rfl)

end Alg

def GeoCutStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (s : MRing ι) (b : K → ℕ) (a : Fin n → K → ℤ) (p : ℕ),
    IsArithVar P (n + 2) → IsMultiHomog s b → s ∉ P → p.Prime →
    ∑ᶠ V ∈ divSupp P (C (p : ℤ)), (multAt (P ⊔ Ideal.span {C (p : ℤ)}) V : ℝ) *
        (geoNum (n + 1) V (Fin.snoc a fun k => (b k : ℤ)) : ℝ) =
      ∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
        ∑ᶠ V ∈ divSupp W (C (p : ℤ)), (multAt (W ⊔ Ideal.span {C (p : ℤ)}) V : ℝ) *
          (geoNum n V a : ℝ)

def DegreeBaseStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (L : Fin 0 → HermLine ι) (p : ℕ), IsArithVar P 1 → p.Prime →
    ptsIntegral P (pot L) (fun _ => 1) =
      ∑ᶠ V ∈ divSupp P (C (p : ℤ)),
        (multAt (P ⊔ Ideal.span {C (p : ℤ)}) V : ℝ) * (geoNum 0 V (fun j => (L j).a) : ℝ)

end ReciprocityTheory.ChartRestriction.G.Geo
