import Formalism.SharpRestriction.GrowthBounds.RootWeights.PolynomialMemWeightSpaceIff

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem fock_form_finset_sum {σ : Type} (F G : MvPolynomial σ K) (s : Finset (σ →₀ ℕ)) (hs : F.support ⊆ s) :
    fock F G = ∑ m ∈ s, F.coeff m * G.coeff m * (expFact m : K) := by
  unfold fock
  refine Finset.sum_subset hs ?_
  intro m _ hm
  rw [MvPolynomial.mem_support_iff, not_not] at hm
  simp [hm]

theorem fock_form_symm {σ : Type} (F G : MvPolynomial σ K) : fock F G = fock G F := by
  classical
  rw [fock_form_finset_sum F G (F.support ∪ G.support) Finset.subset_union_left,
    fock_form_finset_sum G F (F.support ∪ G.support) Finset.subset_union_right]
  exact Finset.sum_congr rfl (fun m _ => by ring)

theorem fock_form_add_right {σ : Type} (F G G' : MvPolynomial σ K) : fock F (G + G') = fock F G + fock F G' := by
  unfold fock
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun m _ => by rw [MvPolynomial.coeff_add]; ring)

theorem fock_form_smul_right {σ : Type} (c : K) (F G : MvPolynomial σ K) : fock F (c • G) = c • fock F G := by
  unfold fock
  rw [smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun m _ => by rw [MvPolynomial.coeff_smul, smul_eq_mul]; ring)

def fockBilinear (K : Type) [Field K] (σ : Type) : MvPolynomial σ K →ₗ[K] MvPolynomial σ K →ₗ[K] K :=
  LinearMap.mk₂ K (fun F G => fock F G)
    (fun F F' G => by
      rw [fock_form_symm, fock_form_add_right, fock_form_symm G F, fock_form_symm G F'])
    (fun c F G => by rw [fock_form_symm, fock_form_smul_right, fock_form_symm G F])
    (fun F G G' => fock_form_add_right F G G')
    (fun c F G => fock_form_smul_right c F G)

theorem fockBilinear_apply {σ : Type} (F G : MvPolynomial σ K) : fockBilinear K σ F G = fock F G := rfl

theorem fock_form_monomial {σ : Type} (m : σ →₀ ℕ) (c : K) (G : MvPolynomial σ K) :
    fock (monomial m c) G = c * G.coeff m * (expFact m : K) := by
  classical
  rw [fock_form_finset_sum _ G {m} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
    MvPolynomial.coeff_monomial, if_pos rfl]

theorem exponent_factorial_add_single_one {σ : Type} [Fintype σ] (u : σ →₀ ℕ) (v : σ) :
    expFact (u + Finsupp.single v 1) = (u v + 1) * expFact u := by
  classical
  unfold expFact
  rw [Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero),
    Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero),
    Fintype.prod_eq_mul_prod_compl v, Fintype.prod_eq_mul_prod_compl v (fun i => (u i).factorial)]
  have h1 : ∀ i ∈ ({v}ᶜ : Finset σ),
      ((u + Finsupp.single v 1 : σ →₀ ℕ) i).factorial = (u i).factorial := by
    intro i hi
    rw [Finset.mem_compl, Finset.mem_singleton] at hi
    simp [Finsupp.single_apply, Ne.symm hi]
  rw [Finset.prod_congr rfl h1]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  ring

theorem fock_mul_adjoint_pderiv {σ : Type} [Fintype σ] (v : σ) (F G : MvPolynomial σ K) :
    fock (X v * F) G = fock F (pderiv v G) := by
  classical
  have addL : ∀ A B C : MvPolynomial σ K, fock (A + B) C = fock A C + fock B C := by
    intro A B C
    rw [fock_form_symm, fock_form_add_right, fock_form_symm C A, fock_form_symm C B]
  induction F using MvPolynomial.induction_on' with
  | monomial m c =>
    induction G using MvPolynomial.induction_on' with
    | monomial n d =>
      rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, MvPolynomial.pderiv_monomial,
        fock_form_monomial, fock_form_monomial, MvPolynomial.coeff_monomial,
        MvPolynomial.coeff_monomial, add_comm (Finsupp.single v 1) m, exponent_factorial_add_single_one]
      by_cases h : n = m + Finsupp.single v 1
      · subst h
        simp only [add_tsub_cancel_right, if_true, Finsupp.add_apply, Finsupp.single_eq_same]
        push_cast
        ring
      · rw [if_neg h]
        by_cases h' : n - Finsupp.single v 1 = m
        · have hv : n v = 0 := by
            by_contra hv
            apply h
            rw [← h', tsub_add_cancel_of_le]
            exact Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hv)
          simp [h', hv]
        · simp [h']
    | add G1 G2 h1 h2 => rw [fock_form_add_right, map_add, fock_form_add_right, h1, h2]
  | add F1 F2 h1 h2 => rw [mul_add, addL, addL, h1, h2]

theorem fock_pderiv_adjoint_mul {σ : Type} [Fintype σ] (v : σ) (F G : MvPolynomial σ K) :
    fock (pderiv v F) G = fock F (X v * G) := by
  rw [fock_form_symm, ← fock_mul_adjoint_pderiv, fock_form_symm]

theorem fock_form_contravariant (LL : Letters ι) (S : Set ι) (a b : Fin n) (F G : MvPolynomial (ι × Fin n) K) :
    fockBilinear K (ι × Fin n) (glOps K n LL S a b F) G = fockBilinear K (ι × Fin n) F (glOps K n LL S b a G) := by
  classical
  simp only [glOps, glAct, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  split_ifs with h1 h2
  · simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, fockBilinear_apply]
    rw [fock_mul_adjoint_pderiv, fock_pderiv_adjoint_mul]
  · simp only [LinearMap.neg_apply, map_neg, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      Derivation.coeFn_coe, fockBilinear_apply]
    rw [fock_mul_adjoint_pderiv, fock_pderiv_adjoint_mul]
  · simp

theorem polynomial_representation_holds : PolynomialGLRepresentation := by
  intro K _ _ ι _ n LL
  exact ⟨fun S => polynomial_isGLRep LL S, fun S S' hd a b c d => disjoint_letters_commute LL S S' hd a b c d,
    fun S S' hs a b => gl_operator_union_add LL S S' hs a b, fun S d a b F hF => gl_operator_preserves_multidegree LL S d a b F hF,
    fun d => homogeneous_multidegree_findim d, fun S mu F hF m hm => weight_vector_monomial_weight LL S mu F hF m hm,
    ⟨fockBilinear K (ι × Fin n), fun F G => rfl, fun S a b F G => fock_form_contravariant LL S a b F G⟩⟩

end Formalism.MainNotions.G.GLWeightTheory
