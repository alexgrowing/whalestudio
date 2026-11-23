import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.BCoreT

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

def qs_cnt {ι : Type*} [Fintype ι] (a : ι → Fin n) (x : Fin n) : ℕ := (univ.filter fun c => a c = x).card

def qs_SM {A : Type*} [CommRing A] (G : Matrix (Fin n) (Fin n) A) (b : ℕ) : Matrix (SymIdx n b) (SymIdx n b) A :=
  fun α β => MvPolynomial.coeff (symMono α) (∏ m : Fin n, (∑ a : Fin n, MvPolynomial.C (G a m) * X a) ^ (β.1 m : ℕ))

lemma qs_sum_cnt {ι : Type*} [Fintype ι] (a : ι → Fin n) : ∑ x, qs_cnt a x = Fintype.card ι := by
  classical
  simp only [qs_cnt]
  rw [← Finset.card_eq_sum_card_fiberwise (f := a) (s := univ) (t := univ) (fun _ _ => by simp)]
  simp

lemma qs_sym_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Type*} [CommRing A] (G : Matrix (Fin n) (Fin n) A)
    (m : ι → Fin n) (β : Fin n → ℕ) (hβ : ∀ x, qs_cnt m x = β x) (α : Fin n →₀ ℕ) :
    MvPolynomial.coeff α (∏ x : Fin n, (∑ a : Fin n, MvPolynomial.C (G a x) * X a) ^ (β x)) =
      ∑ a : ι → Fin n, if (∀ x, qs_cnt a x = α x) then ∏ c, G (a c) (m c) else 0 := by
  classical
  have h1 : (∏ x : Fin n, (∑ a : Fin n, (MvPolynomial.C (G a x) * X a : MvPolynomial (Fin n) A)) ^ (β x)) =
      ∏ c : ι, ∑ a : Fin n, MvPolynomial.C (G a (m c)) * X a := by
    rw [← Finset.prod_fiberwise (s := univ) (g := m)]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [Finset.prod_congr rfl (g := fun _ => ∑ a : Fin n, (MvPolynomial.C (G a x) * X a : MvPolynomial (Fin n) A))
      (fun c hc => by rw [(Finset.mem_filter.1 hc).2]), Finset.prod_const, ← hβ x]
    rfl
  rw [h1, Fintype.prod_sum, MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h2 : (∏ c : ι, (MvPolynomial.C (G (a c) (m c)) * X (a c) : MvPolynomial (Fin n) A)) =
      MvPolynomial.monomial (∑ c : ι, Finsupp.single (a c) 1) (∏ c, G (a c) (m c)) := by
    rw [MvPolynomial.monomial_sum_prod]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [MvPolynomial.C_mul_X_eq_monomial]
  rw [h2, MvPolynomial.coeff_monomial]
  have h3 : (∑ c : ι, Finsupp.single (a c) 1 = α) ↔ ∀ x, qs_cnt a x = α x := by
    rw [Finsupp.ext_iff]
    refine forall_congr' fun x => ?_
    rw [Finsupp.finsetSum_apply, qs_cnt, Finset.card_filter]
    simp only [Finsupp.single_apply]
  simp only [h3]

def qs_mon {ι : Type*} [Fintype ι] {b : ℕ} (hb : Fintype.card ι = b) (m : ι → Fin n) : SymIdx n b :=
  ⟨fun x => ⟨qs_cnt m x, by
    have := qs_sum_cnt m
    have h2 : qs_cnt m x ≤ ∑ x, qs_cnt m x := Finset.single_le_sum (f := qs_cnt m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
    omega⟩, by simpa using (qs_sum_cnt m).trans hb⟩

theorem qs_sum_sym {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Type*} [CommRing A] (G : Matrix (Fin n) (Fin n) A) {b : ℕ}
    (hb : Fintype.card ι = b) (m : ι → Fin n) (α : SymIdx n b) (r : A) :
    ∑ β : SymIdx n b, qs_SM G b α β * (if (∀ x, qs_cnt m x = (β.1 x : ℕ)) then r else 0) =
      (∑ a : ι → Fin n, if (∀ x, qs_cnt a x = (α.1 x : ℕ)) then ∏ c, G (a c) (m c) else 0) * r := by
  classical
  rw [Finset.sum_eq_single (qs_mon hb m)]
  · have h0 : ∀ x, qs_cnt m x = ((qs_mon hb m).1 x : ℕ) := fun x => rfl
    rw [if_pos h0]
    congr 1
    exact qs_sym_mul G m _ h0 (symMono α)
  · intro β _ hβ
    rw [if_neg, mul_zero]
    intro h
    exact hβ (Subtype.ext (funext fun x => Fin.ext (h x).symm))
  · intro h; exact absurd (Finset.mem_univ _) h

def qs_gC (n : ℕ) : Matrix (Fin n) (Fin n) (GLCoord ℤ n) :=
  Matrix.of fun a b => algebraMap _ (GLCoord ℤ n) (genMat ℤ n a b)

def qs_gI (n : ℕ) : Matrix (Fin n) (Fin n) (GLCoord ℤ n) := Matrix.of fun a b => ginvC n a b

lemma qs_SymMat_eq (n b : ℕ) : SymMat n b = qs_SM (qs_gC n) b := rfl

lemma qs_SymDMat_eq (n b : ℕ) : SymDMat n b = qs_SM (qs_gI n).transpose b := rfl

lemma qs_gC_mul_gI (n : ℕ) : qs_gC n * qs_gI n = 1 := by
  have h1 : qs_gC n = (genMat ℤ n).map (algebraMap _ (GLCoord ℤ n)) := rfl
  have h2 : qs_gI n = (((detU n)⁻¹ : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) •
      ((genMat ℤ n).adjugate).map (algebraMap _ (GLCoord ℤ n)) := by
    ext a b; simp [qs_gI, ginvC]
  rw [h1, h2, Matrix.mul_smul, ← Matrix.map_mul, Matrix.mul_adjugate]
  ext a b
  by_cases hab : a = b
  · subst hab
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    exact (detU n).inv_mul
  · simp [Matrix.one_apply_ne hab]

lemma qs_SM_diag {A : Type*} [CommRing A] (d : Fin n → A) (b : ℕ) (α β : SymIdx n b) :
    qs_SM (Matrix.diagonal d) b α β = if α = β then ∏ x, d x ^ (β.1 x : ℕ) else 0 := by
  classical
  have h1 : ∀ x : Fin n, (∑ a : Fin n, (MvPolynomial.C (Matrix.diagonal d a x) * X a : MvPolynomial (Fin n) A)) =
      MvPolynomial.monomial (Finsupp.single x 1) (d x) := by
    intro x
    rw [Finset.sum_eq_single x]
    · rw [Matrix.diagonal_apply_eq, MvPolynomial.C_mul_X_eq_monomial]
    · intro a _ ha; rw [Matrix.diagonal_apply_ne _ ha]; simp
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [qs_SM]
  simp_rw [h1, MvPolynomial.monomial_pow]
  rw [← MvPolynomial.monomial_sum_prod, MvPolynomial.coeff_monomial]
  have h3 : (∑ x : Fin n, (β.1 x : ℕ) • Finsupp.single x 1 = symMono α) ↔ α = β := by
    rw [Finsupp.ext_iff]
    constructor
    · intro h
      refine Subtype.ext (funext fun x => Fin.ext ?_)
      have := h x
      rw [Finsupp.finsetSum_apply] at this
      simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
      exact this.symm
    · rintro rfl x
      rw [Finsupp.finsetSum_apply]
      simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rfl
  simp only [h3]

lemma qs_SM_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (G : Matrix (Fin n) (Fin n) A) (b : ℕ)
    (α β : SymIdx n b) : f (qs_SM G b α β) = qs_SM (G.map f) b α β := by
  rw [qs_SM, qs_SM, ← MvPolynomial.coeff_map]
  simp [map_prod, map_pow, map_sum]

end Formalism.InvariantFactorPaths.ColumnFamilies
