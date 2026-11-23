import Mathlib

noncomputable section

open MvPolynomial TensorProduct

namespace ReciprocityTheory.PGsh

section Bialg

variable {R A : Type*} [CommRing R] [CommRing A] [Bialgebra R A]

def IsPtDer (δ : A →ₗ[R] R) : Prop :=
  ∀ f g : A, δ (f * g) = Coalgebra.counit (R := R) f * δ g + Coalgebra.counit (R := R) g * δ f

def convD (δ : A →ₗ[R] R) : A →ₗ[R] A :=
  (TensorProduct.rid R A).toLinearMap ∘ₗ δ.lTensor A ∘ₗ Coalgebra.comul

private lemma rid_convolution_derivation (δ : A →ₗ[R] R) (hδ : IsPtDer δ) (u v : A ⊗[R] A) :
    (TensorProduct.rid R A) (δ.lTensor A (u * v)) =
      (TensorProduct.rid R A) ((Coalgebra.counit (R := R) (A := A)).lTensor A u) *
          (TensorProduct.rid R A) (δ.lTensor A v) +
        (TensorProduct.rid R A) (δ.lTensor A u) *
          (TensorProduct.rid R A) ((Coalgebra.counit (R := R) (A := A)).lTensor A v) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u u' hu hu' => simp only [add_mul, map_add, hu, hu']; ring
  | tmul a b =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add v v' hv hv' => simp only [mul_add, map_add, hv, hv']; ring
    | tmul c e =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.lTensor_tmul,
        TensorProduct.rid_tmul, hδ b e, Algebra.smul_def, map_add, map_mul]
      ring

lemma convD_mul (δ : A →ₗ[R] R) (hδ : IsPtDer δ) (f g : A) :
    convD δ (f * g) = f * convD δ g + g * convD δ f := by
  have hE : ∀ a : A, (TensorProduct.rid R A)
      ((Coalgebra.counit (R := R) (A := A)).lTensor A (Coalgebra.comul a)) = a := by
    intro a; rw [Coalgebra.lTensor_counit_comul]; simp
  simp only [convD, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    Bialgebra.comul_mul]
  rw [rid_convolution_derivation δ hδ, hE, hE]; ring

lemma counit_convD (δ : A →ₗ[R] R) (f : A) :
    Coalgebra.counit (R := R) (convD δ f) = δ f := by
  have key : ∀ u : A ⊗[R] A, Coalgebra.counit (R := R) ((TensorProduct.rid R A) (δ.lTensor A u)) =
      δ ((TensorProduct.lid R A) ((Coalgebra.counit (R := R) (A := A)).rTensor A u)) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => simp only [map_add, hu, hv]
    | tmul a b => simp [mul_comm]
  simp only [convD, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, key,
    Coalgebra.rTensor_counit_comul]
  simp

lemma convD_groupLike (δ : A →ₗ[R] R) {χ : A} (h : IsGroupLikeElem R χ) :
    convD δ χ = δ χ • χ := by
  simp [convD, h.comul_eq_tmul_self]

lemma IsPtDer.map_one {δ : A →ₗ[R] R} (hδ : IsPtDer δ) : δ 1 = 0 := by
  have h := hδ 1 1
  simp only [mul_one, Bialgebra.counit_one, one_mul] at h
  linear_combination -h

lemma IsPtDer.map_sq {δ : A →ₗ[R] R} (hδ : IsPtDer δ) {f : A}
    (hf : f ∈ RingHom.ker (Bialgebra.counitAlgHom R A) ^ 2) : δ f = 0 := by
  rw [pow_two] at hf
  refine Submodule.mul_induction_on hf ?_ ?_
  · intro a ha b hb
    rw [RingHom.mem_ker, Bialgebra.counitAlgHom_apply] at ha hb
    rw [hδ, ha, hb]; ring
  · intro a b ha hb; rw [map_add, ha, hb, add_zero]

end Bialg

section Chain

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

lemma map_aeval_of_leibniz {d : ℕ} (D : A →ₗ[R] A) (hD : ∀ f g, D (f * g) = f * D g + g * D f)
    (x : Fin d → A) (P : MvPolynomial (Fin d) R) :
    D (aeval x P) = ∑ j, aeval x (pderiv j P) * D (x j) := by
  classical
  have h1 : D 1 = 0 := by
    have h := hD 1 1
    simp only [one_mul] at h
    linear_combination -h
  induction P using MvPolynomial.induction_on with
  | C a => simp [Algebra.algebraMap_eq_smul_one, h1]
  | add P Q hP hQ => simp only [map_add, hP, hQ, add_mul, Finset.sum_add_distrib]
  | mul_X P n hP =>
    have hs : ∑ j, aeval x (pderiv j (P * X n)) * D (x j) =
        x n * ∑ j, aeval x (pderiv j P) * D (x j) + aeval x P * D (x n) := by
      have : ∀ j, aeval x (pderiv j (P * X n)) * D (x j) =
          x n * (aeval x (pderiv j P) * D (x j)) + aeval x P * (aeval x (pderiv j (X n : MvPolynomial (Fin d) R)) * D (x j)) := by
        intro j
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, aeval_X]
        ring
      rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum]
      congr 2
      rw [Finset.sum_eq_single n]
      · simp
      · intro j _ hj; rw [pderiv_X_of_ne (Ne.symm hj)]; simp
      · simp
    rw [hs, map_mul, aeval_X, hD, hP]; ring

end Chain

section Coeff

variable {R : Type*} [CommRing R] {d p : ℕ}

def LowRed (p m : ℕ) (P : MvPolynomial (Fin d) R) : Prop :=
  ∀ β : Fin d →₀ ℕ, (∀ j, β j < p) → β.degree < m → coeff β P = 0

lemma lowRed_mul {m : ℕ} {F G : MvPolynomial (Fin d) R} (hF : LowRed p m F)
    (hG : constantCoeff G = 0) (β : Fin d →₀ ℕ) (hβ : ∀ j, β j < p) (hdeg : β.degree ≤ m) :
    coeff β (F * G) = 0 := by
  classical
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun y hy => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hy
  by_cases h2 : y.2 = 0
  · rw [h2, ← congrFun constantCoeff_eq G, hG, mul_zero]
  · have hle : ∀ j, y.1 j ≤ β j := fun j => by rw [← hy]; simp
    have h2' : y.2.degree ≠ 0 := fun h => h2 ((Finsupp.degree_eq_zero_iff _).1 h)
    have hdeg1 : y.1.degree < β.degree := by
      rw [← hy, map_add]; omega
    rw [hF y.1 (fun j => lt_of_le_of_lt (hle j) (hβ j)) (by omega), zero_mul]

lemma lowRed_pderiv {m : ℕ} (hp0 : (p : R) = 0) {P : MvPolynomial (Fin d) R}
    (hP : LowRed p (m + 1) P) (j : Fin d) : LowRed p m (pderiv j P) := by
  classical
  intro γ hγ hdeg
  rw [coeff_pderiv]
  by_cases hlt : γ j + 1 < p
  · rw [hP, zero_mul]
    · intro i
      by_cases hij : i = j
      · subst hij; simpa using hlt
      · simpa [Finsupp.single_apply, Ne.symm hij] using hγ i
    · rw [map_add, Finsupp.degree_single]; omega
  · have h : γ j + 1 = p := by have := hγ j; omega
    have hc : ((γ j : R) + 1) = 0 := by
      have : ((γ j + 1 : ℕ) : R) = 0 := by rw [h, hp0]
      exact_mod_cast this
    rw [hc, mul_zero]

end Coeff

section Bialg2

variable {R A : Type*} [CommRing R] [CommRing A] [Bialgebra R A]

lemma isPtDer_of {δ : A →ₗ[R] R} (h1 : δ 1 = 0)
    (h2 : ∀ f ∈ RingHom.ker (Bialgebra.counitAlgHom R A) ^ 2, δ f = 0) : IsPtDer δ := by
  intro f g
  set a := Coalgebra.counit (R := R) f
  set b := Coalgebra.counit (R := R) g
  have hf : f - algebraMap R A a ∈ RingHom.ker (Bialgebra.counitAlgHom R A) := by
    simp [RingHom.mem_ker, a]
  have hg : g - algebraMap R A b ∈ RingHom.ker (Bialgebra.counitAlgHom R A) := by
    simp [RingHom.mem_ker, b]
  have hfg := h2 _ (by rw [pow_two]; exact Ideal.mul_mem_mul hf hg)
  have e : f * g = (f - algebraMap R A a) * (g - algebraMap R A b) + a • g + b • f - (a * b) • 1 := by
    simp only [Algebra.smul_def, map_mul, mul_one]; ring
  rw [e, map_sub, map_add, map_add, hfg, map_smul, map_smul, map_smul, h1, smul_eq_mul,
    smul_eq_mul, smul_eq_mul]
  ring

end Bialg2

section Core

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {d p : ℕ}

lemma mem_span_pow_of_coeff {P : MvPolynomial (Fin d) R}
    (h : ∀ β : Fin d →₀ ℕ, (∀ j, β j < p) → coeff β P = 0) :
    P ∈ Ideal.span (Set.range fun j : Fin d => (X j : MvPolynomial (Fin d) R) ^ p) := by
  classical
  rw [P.as_sum]
  refine Ideal.sum_mem _ fun β hβ => ?_
  have hnot : ¬ ∀ j, β j < p := fun h' => (mem_support_iff.1 hβ) (h β h')
  push Not at hnot
  obtain ⟨j, hj⟩ := hnot
  have e : monomial β (coeff β P) = X j ^ p * monomial (β - Finsupp.single j p) (coeff β P) := by
    have hs : Finsupp.single j p + (β - Finsupp.single j p) = β := by
      ext l
      by_cases hl : j = l
      · subst hl
        simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
          Finsupp.single_eq_same]
        omega
      · simp [hl]
    rw [X_pow_eq_monomial, monomial_mul, one_mul, hs]
  rw [e]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨j, rfl⟩)

lemma aeval_eq_zero_of_mem_span (x : Fin d → A) (hxp : ∀ j, x j ^ p = 0)
    {P : MvPolynomial (Fin d) R}
    (hP : P ∈ Ideal.span (Set.range fun j : Fin d => (X j : MvPolynomial (Fin d) R) ^ p)) :
    aeval x P = 0 := by
  have hle : Ideal.span (Set.range fun j : Fin d => (X j : MvPolynomial (Fin d) R) ^ p) ≤
      RingHom.ker (aeval (R := R) x) := by
    rw [Ideal.span_le, Set.range_subset_iff]
    intro j
    simp [RingHom.mem_ker, hxp j]
  exact hle hP

theorem coeff_eq_zero_of_stable (ε : A →ₐ[R] R) (x : Fin d → A) (hx : ∀ i, ε (x i) = 0)
    (D : Fin d → A →ₗ[R] A) (hD : ∀ i f g, D i (f * g) = f * D i g + g * D i f)
    (hDx : ∀ i j, ε (D i (x j)) = if i = j then 1 else 0)
    (hsurj : Function.Surjective (aeval (R := R) x))
    (hp0 : (p : R) = 0) (hunit : ∀ n, 0 < n → n < p → IsUnit (n : R))
    (K : Set A) (hK : ∀ a ∈ K, ε a = 0) (hKD : ∀ i, ∀ a ∈ K, D i a ∈ K)
    (P : MvPolynomial (Fin d) R) (hP : aeval x P ∈ K) :
    ∀ β : Fin d →₀ ℕ, (∀ j, β j < p) → coeff β P = 0 := by
  classical
  have hε : ∀ Q : MvPolynomial (Fin d) R, ε (aeval x Q) = constantCoeff Q := by
    intro Q
    have e : ε.comp (aeval x) = aeval (fun _ => (0 : R)) := by
      rw [comp_aeval]; congr 1; funext i; exact hx i
    rw [← AlgHom.comp_apply, e, aeval_zero']
    rfl
  have Z : ∀ m, ∀ Q : MvPolynomial (Fin d) R, aeval x Q ∈ K → LowRed p m Q →
      ∀ α : Fin d →₀ ℕ, (∀ j, α j < p) → α.degree = m → coeff α Q = 0 := by
    intro m
    induction m with
    | zero =>
      intro Q hQ _ α _ hα
      have h0 : α = 0 := (Finsupp.degree_eq_zero_iff α).1 hα
      subst h0
      rw [← congrFun constantCoeff_eq Q, ← hε, hK _ hQ]
    | succ m ih =>
      intro Q hQ hlow α hα hdeg
      obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
        by_contra h
        push Not at h
        have h0 : α = 0 := Finsupp.ext h
        subst h0
        simp at hdeg
      set β := α - Finsupp.single i 1 with hβdef
      have hαβ : α = β + Finsupp.single i 1 := by
        ext j
        simp only [hβdef, Finsupp.coe_add, Pi.add_apply, Finsupp.coe_tsub, Pi.sub_apply,
          Finsupp.single_apply]
        split_ifs with hj
        · subst hj; omega
        · omega
      choose T hT using fun j => hsurj (D i (x j))
      have hTc : ∀ j, constantCoeff (T j) = if i = j then 1 else 0 := fun j => by
        rw [← hε, hT, hDx]
      set Q' : MvPolynomial (Fin d) R := ∑ j, pderiv j Q * T j with hQ'def
      have hQ' : aeval x Q' ∈ K := by
        have e : aeval x Q' = D i (aeval x Q) := by
          rw [map_aeval_of_leibniz (D i) (hD i), hQ'def, map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_mul, hT]
        rw [e]; exact hKD i _ hQ
      have hsplit : ∀ j (γ : Fin d →₀ ℕ), γ.degree ≤ m → (∀ l, γ l < p) →
          coeff γ (pderiv j Q * T j) = coeff γ (pderiv j Q) * (if i = j then 1 else 0) := by
        intro j γ hγd hγ
        have e : T j = C (constantCoeff (T j)) + (T j - C (constantCoeff (T j))) := by ring
        rw [e, mul_add, coeff_add, mul_comm (pderiv j Q) (C _), coeff_C_mul,
          lowRed_mul (G := T j - C (constantCoeff (T j))) (lowRed_pderiv hp0 hlow j) (by simp) γ hγ hγd,
          add_zero, hTc, mul_comm]
      have hlow' : LowRed p m Q' := by
        intro γ hγ hγd
        rw [hQ'def, coeff_sum]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [hsplit j γ hγd.le hγ, lowRed_pderiv hp0 hlow j γ hγ hγd, zero_mul]
      have hβr : ∀ j, β j < p := fun j =>
        lt_of_le_of_lt (by rw [hβdef]; exact tsub_le_self) (hα j)
      have hβd : β.degree = m := by
        have := congrArg Finsupp.degree hαβ
        rw [map_add, Finsupp.degree_single] at this
        omega
      have h0 := ih Q' hQ' hlow' β hβr hβd
      rw [hQ'def, coeff_sum, Finset.sum_eq_single i] at h0
      · rw [hsplit i β hβd.le hβr, if_pos rfl, mul_one, coeff_pderiv, ← hαβ] at h0
        have hb : α i = β i + 1 := by rw [hαβ]; simp
        have hu : IsUnit ((β i : R) + 1) := by
          have := hunit (α i) (Nat.pos_of_ne_zero hi) (hα i)
          rw [hb] at this
          exact_mod_cast this
        exact (hu.mul_left_eq_zero).1 h0
      · intro j _ hj
        rw [hsplit j β hβd.le hβr, if_neg (Ne.symm hj), mul_zero]
      · simp
  have W : ∀ m, ∀ Q : MvPolynomial (Fin d) R, aeval x Q ∈ K → LowRed p m Q := by
    intro m
    induction m with
    | zero => intro Q _ β _ h; simp at h
    | succ m ih =>
      intro Q hQ β hβ hd
      rcases Nat.lt_succ_iff_lt_or_eq.1 hd with h | h
      · exact ih Q hQ β hβ h
      · exact Z m Q hQ (ih Q hQ) β hβ h
  intro β hβ
  exact W (β.degree + 1) P hP β hβ (Nat.lt_succ_self _)

end Core

end ReciprocityTheory.PGsh
