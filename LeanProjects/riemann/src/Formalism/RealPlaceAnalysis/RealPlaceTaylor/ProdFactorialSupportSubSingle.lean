import Formalism.RealPlaceAnalysis.FockPairGl

open MvPolynomial

noncomputable section

namespace Formalism.REAL

section general

variable {σ : Type*}

lemma fischerInner_eq_sum_of_subset (f g : MvPolynomial σ ℂ) (s : Finset (σ →₀ ℕ)) (h : f.support ⊆ s) :
    fockF f g = ∑ m ∈ s, f.coeff m * star (g.coeff m) *
      ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold fockF
  apply Finset.sum_subset h
  intro m _ hm
  simp [MvPolynomial.notMem_support_iff.mp hm]

lemma fischerInner_add_left (f1 f2 g : MvPolynomial σ ℂ) :
    fockF (f1 + f2) g = fockF f1 g + fockF f2 g := by
  classical
  rw [fischerInner_eq_sum_of_subset _ _ (f1.support ∪ f2.support) MvPolynomial.support_add,
    fischerInner_eq_sum_of_subset f1 g (f1.support ∪ f2.support) Finset.subset_union_left,
    fischerInner_eq_sum_of_subset f2 g (f1.support ∪ f2.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [coeff_add]; ring

lemma fischerInner_add_right (f g1 g2 : MvPolynomial σ ℂ) :
    fockF f (g1 + g2) = fockF f g1 + fockF f g2 := by
  unfold fockF
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [coeff_add, star_add]; ring

def fischerInnerLeftHom (g : MvPolynomial σ ℂ) : MvPolynomial σ ℂ →+ ℂ :=
  AddMonoidHom.mk' (fun f => fockF f g) (fun a b => fischerInner_add_left a b g)

def fischerInnerRightHom (f : MvPolynomial σ ℂ) : MvPolynomial σ ℂ →+ ℂ :=
  AddMonoidHom.mk' (fun g => fockF f g) (fun a b => fischerInner_add_right f a b)

lemma fischerInner_sum_left {ι : Type*} (s : Finset ι) (h : ι → MvPolynomial σ ℂ) (g : MvPolynomial σ ℂ) :
    fockF (∑ a ∈ s, h a) g = ∑ a ∈ s, fockF (h a) g :=
  map_sum (fischerInnerLeftHom g) h s

lemma fischerInner_sum_right {ι : Type*} (s : Finset ι) (f : MvPolynomial σ ℂ) (h : ι → MvPolynomial σ ℂ) :
    fockF f (∑ a ∈ s, h a) = ∑ a ∈ s, fockF f (h a) :=
  map_sum (fischerInnerRightHom f) h s

lemma fischerInner_neg_left (f g : MvPolynomial σ ℂ) : fockF (-f) g = -fockF f g :=
  map_neg (fischerInnerLeftHom g) f

lemma fischerInner_neg_right (f g : MvPolynomial σ ℂ) : fockF f (-g) = -fockF f g :=
  map_neg (fischerInnerRightHom f) g

lemma fischerInner_eq_star (f g : MvPolynomial σ ℂ) : fockF f g = star (fockF g f) := by
  classical
  rw [fischerInner_eq_sum_of_subset f g (f.support ∪ g.support) Finset.subset_union_left,
    fischerInner_eq_sum_of_subset g f (f.support ∪ g.support) Finset.subset_union_right, star_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [star_mul', star_star, star_natCast]; ring

lemma fischerInner_monomial_left (u : σ →₀ ℕ) (c : ℂ) (g : MvPolynomial σ ℂ) :
    fockF (monomial u c) g = c * star (g.coeff u) * ((∏ k ∈ u.support, (u k).factorial : ℕ) : ℂ) := by
  classical
  rw [fischerInner_eq_sum_of_subset _ _ {u} support_monomial_subset, Finset.sum_singleton, coeff_monomial,
    if_pos rfl]

lemma prod_factorial_support_sub_single [DecidableEq σ] (u : σ →₀ ℕ) (v : σ) (hv : u v ≠ 0) :
    (∏ k ∈ u.support, (u k).factorial) =
      u v * ∏ k ∈ (u - Finsupp.single v 1 : σ →₀ ℕ).support, ((u - Finsupp.single v 1 : σ →₀ ℕ) k).factorial := by
  have hsub : (u - Finsupp.single v 1 : σ →₀ ℕ).support ⊆ u.support := by
    intro k hk
    rw [Finsupp.mem_support_iff] at hk ⊢
    intro h0; apply hk; simp [Finsupp.tsub_apply, h0]
  have e : ∏ k ∈ (u - Finsupp.single v 1 : σ →₀ ℕ).support, ((u - Finsupp.single v 1 : σ →₀ ℕ) k).factorial =
      ∏ k ∈ u.support, ((u - Finsupp.single v 1 : σ →₀ ℕ) k).factorial :=
    Finset.prod_subset hsub (fun k _ hk => by rw [Finsupp.notMem_support_iff.mp hk]; rfl)
  rw [e]
  have hmem : v ∈ u.support := Finsupp.mem_support_iff.mpr hv
  rw [← Finset.mul_prod_erase _ _ hmem, ← Finset.mul_prod_erase _ _ hmem]
  have h2 : ∏ k ∈ u.support.erase v, ((u - Finsupp.single v 1 : σ →₀ ℕ) k).factorial =
      ∏ k ∈ u.support.erase v, (u k).factorial := by
    refine Finset.prod_congr rfl fun k hk => ?_
    have hk' : k ≠ v := Finset.ne_of_mem_erase hk
    simp [Finsupp.tsub_apply, Finsupp.single_apply, Ne.symm hk']
  rw [h2, ← mul_assoc]
  congr 1
  simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
  exact (Nat.mul_factorial_pred hv).symm

lemma fischerInner_pderiv_left [DecidableEq σ] (v : σ) (f g : MvPolynomial σ ℂ) :
    fockF (pderiv v f) g = fockF f (X v * g) := by
  induction f using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [pderiv_monomial, fischerInner_monomial_left, fischerInner_monomial_left, coeff_X_mul']
    by_cases hv : u v = 0
    · have : v ∉ u.support := Finsupp.notMem_support_iff.mpr hv
      simp [hv, this]
    · have : v ∈ u.support := Finsupp.mem_support_iff.mpr hv
      rw [if_pos this, prod_factorial_support_sub_single u v hv]
      push_cast; ring
  | add p q hp hq => rw [map_add, fischerInner_add_left, fischerInner_add_left, hp, hq]

lemma fischerInner_X_mul_left [DecidableEq σ] (v : σ) (f g : MvPolynomial σ ℂ) :
    fockF (X v * f) g = fockF f (pderiv v g) := by
  rw [fischerInner_eq_star, ← fischerInner_pderiv_left, ← fischerInner_eq_star]

end general

variable {M n' : ℕ}

lemma fischerInner_oscillatorLower (ε : Fin M → Bool) (ε' : Fin n' → Bool) (i : Fin M) (a : Fin n')
    (f g : MvPolynomial (Fin M × Fin n') ℂ) :
    fockF (bop ε ε' i a f) g = (if sgnv ε ε' i a then 1 else -1) * fockF f (bpl ε ε' i a g) := by
  unfold bop bpl
  split_ifs with h
  · simp only [LinearMap.mulLeft_apply, Derivation.coeFn_coe, one_mul]
    exact fischerInner_pderiv_left _ f g
  · simp only [LinearMap.mulLeft_apply, LinearMap.neg_apply, Derivation.coeFn_coe, fischerInner_neg_right]
    rw [fischerInner_X_mul_left]; ring

lemma fischerInner_oscillatorRaise (ε : Fin M → Bool) (ε' : Fin n' → Bool) (i : Fin M) (a : Fin n')
    (f g : MvPolynomial (Fin M × Fin n') ℂ) :
    fockF (bpl ε ε' i a f) g = (if sgnv ε ε' i a then 1 else -1) * fockF f (bop ε ε' i a g) := by
  unfold bop bpl
  split_ifs with h
  · simp only [LinearMap.mulLeft_apply, Derivation.coeFn_coe, one_mul]
    exact fischerInner_X_mul_left _ f g
  · simp only [LinearMap.mulLeft_apply, LinearMap.neg_apply, Derivation.coeFn_coe, fischerInner_neg_left]
    rw [fischerInner_pderiv_left]; ring

lemma signMatch_mul_left (ε : Fin M → Bool) (ε' : Fin n' → Bool) (i j : Fin M) (a : Fin n') :
    ((if sgnv ε ε' i a then 1 else -1 : ℂ) * (if sgnv ε ε' j a then 1 else -1)) =
      ((sgn ε i j : ℝ) : ℂ) := by
  unfold sgnv sgn
  generalize ε i = x; generalize ε j = y; generalize ε' a = z
  cases x <;> cases y <;> cases z <;> norm_num

lemma signMatch_mul_right (ε : Fin M → Bool) (ε' : Fin n' → Bool) (i : Fin M) (a b : Fin n') :
    ((if sgnv ε ε' i b then 1 else -1 : ℂ) * (if sgnv ε ε' i a then 1 else -1)) =
      ((sgn ε' a b : ℝ) : ℂ) := by
  unfold sgnv sgn
  generalize ε i = x; generalize ε' a = y; generalize ε' b = z
  cases x <;> cases y <;> cases z <;> norm_num

theorem fischerAdjointness_holds : FockAdj := by
  intro M n' ε ε' f g
  refine ⟨fun i a => fischerInner_oscillatorLower ε ε' i a f g, fun i j => ?_, fun a b => ?_⟩
  · simp only [Eg, LinearMap.sum_apply, Module.End.mul_apply, fischerInner_sum_left,
      fischerInner_sum_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [fischerInner_oscillatorRaise, fischerInner_oscillatorLower, ← mul_assoc, signMatch_mul_left]
  · simp only [Eg', LinearMap.neg_apply, LinearMap.sum_apply, Module.End.mul_apply,
      fischerInner_neg_left, fischerInner_neg_right, fischerInner_sum_left, fischerInner_sum_right, mul_neg, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fischerInner_oscillatorRaise, fischerInner_oscillatorLower, ← mul_assoc, signMatch_mul_right]

end Formalism.REAL
