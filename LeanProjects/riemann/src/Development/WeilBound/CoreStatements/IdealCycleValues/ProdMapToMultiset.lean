import Mathlib

open MvPolynomial

namespace BaseChangeColon

noncomputable section

variable {σ σ' G : Type}

def evL (φ : (σ →₀ ℕ) → ℝ) : MvPolynomial σ ℝ →ₗ[ℝ] ℝ := (basisMonomials σ ℝ).constr ℝ φ

theorem evL_monomial (φ : (σ →₀ ℕ) → ℝ) (μ : σ →₀ ℕ) (c : ℝ) :
    evL φ (monomial μ c) = c * φ μ := by
  have hm : monomial μ c = c • (basisMonomials σ ℝ) μ := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [evL, hm, map_smul, Module.Basis.constr_basis, smul_eq_mul]

theorem evL_eq (φ : (σ →₀ ℕ) → ℝ) (H : MvPolynomial σ ℝ) :
    ∑ μ ∈ H.support, H.coeff μ * φ μ = evL φ H := by
  conv_rhs => rw [H.as_sum]
  rw [map_sum]
  exact Finset.sum_congr rfl (fun μ _ => (evL_monomial φ μ _).symm)

theorem evL_C_mul (φ : (σ →₀ ℕ) → ℝ) (c : ℝ) (H : MvPolynomial σ ℝ) :
    evL φ (C c * H) = c * evL φ H := by
  rw [C_mul', map_smul, smul_eq_mul]

theorem evL_rename (e : σ → σ') (φ : (σ' →₀ ℕ) → ℝ) (H : MvPolynomial σ ℝ) :
    evL φ (rename e H) = evL (fun μ => φ (μ.mapDomain e)) H := by
  refine MvPolynomial.induction_on' H (fun μ c => ?_) (fun p q hp hq => ?_)
  · rw [rename_monomial, evL_monomial, evL_monomial]
  · rw [map_add, map_add, map_add, hp, hq]

theorem classes_mapDomain (e : σ → σ') (cls : σ' → G) (μ : σ →₀ ℕ) :
    ((μ.mapDomain e).toMultiset.map cls).toList = (μ.toMultiset.map (cls ∘ e)).toList := by
  rw [← Finsupp.toMultiset_map, Multiset.map_map]

theorem classes_add_perm (cls : σ → G) (ν μ : σ →₀ ℕ) (Q : List G) :
    (((ν + μ).toMultiset.map cls).toList ++ Q).Perm
      ((ν.toMultiset.map cls).toList ++ ((μ.toMultiset.map cls).toList ++ Q)) := by
  rw [← Multiset.coe_eq_coe, ← Multiset.coe_add, ← Multiset.coe_add, ← Multiset.coe_add]
  simp only [Multiset.coe_toList, map_add, Multiset.map_add, add_assoc]

theorem evL_mul (n : List G → ℝ) (hp : ∀ l l', l.Perm l' → n l = n l') (cls : σ → G)
    (H P : MvPolynomial σ ℝ) (Q : List G) :
    evL (fun μ => n ((μ.toMultiset.map cls).toList ++ Q)) (H * P) =
      evL (fun μ => evL (fun ν => n ((ν.toMultiset.map cls).toList ++
        ((μ.toMultiset.map cls).toList ++ Q))) H) P := by
  refine MvPolynomial.induction_on' P (fun μ b => ?_) (fun p q ih1 ih2 => ?_)
  · simp only [evL_monomial]
    refine MvPolynomial.induction_on' H (fun ν a => ?_) (fun p q ih1 ih2 => ?_)
    · simp only [monomial_mul, evL_monomial]
      rw [hp _ _ (classes_add_perm cls ν μ Q)]
      ring
    · rw [add_mul, map_add, ih1, ih2, map_add]
      ring
  · rw [mul_add, map_add, ih1, ih2, map_add]

theorem evL_mul_X (n : List G → ℝ) (hp : ∀ l l', l.Perm l' → n l = n l') (cls : σ → G)
    (H : MvPolynomial σ ℝ) (i : σ) (Q : List G) :
    evL (fun μ => n ((μ.toMultiset.map cls).toList ++ Q)) (H * X i) =
      evL (fun μ => n ((μ.toMultiset.map cls).toList ++ (cls i :: Q))) H := by
  rw [evL_mul n hp cls H (X i) Q, X, evL_monomial, one_mul]
  simp only [Finsupp.toMultiset_single, one_nsmul, Multiset.map_singleton, Multiset.toList_singleton,
    List.singleton_append]

theorem prod_map_toMultiset {A : Type} [CommMonoid A] (f : σ → A) (μ : σ →₀ ℕ) :
    (μ.toMultiset.map f).prod = μ.prod fun a k => f a ^ k := by
  rw [Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
    Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]

theorem subst_multiset [AddCommGroup G] [Fintype σ] (d : ℕ) (n : List G → ℝ)
    (hp : ∀ l l', l.Perm l' → n l = n l')
    (ha : ∀ b b' l, l.length + 1 = d → n ((b + b') :: l) = n (b :: l) + n (b' :: l))
    (cls : σ → G) (M : σ' → σ → ℤ) (s : Multiset σ') :
    ∀ Q : List G, s.card + Q.length = d →
      n ((s.map fun t => ∑ i, M t i • cls i).toList ++ Q) =
        evL (fun μ => n ((μ.toMultiset.map cls).toList ++ Q))
          (s.map fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)).prod := by
  have hlin : ∀ (l : List G), l.length + 1 = d → ∀ k : σ → ℤ,
      n ((∑ i, k i • cls i) :: l) = ∑ i, (k i : ℝ) * n (cls i :: l) := by
    intro l hl k
    let f : G →+ ℝ := AddMonoidHom.mk' (fun b => n (b :: l)) (fun b b' => ha b b' l hl)
    have hf : ∀ b, f b = n (b :: l) := fun _ => rfl
    rw [← hf, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_zsmul, zsmul_eq_mul, hf]
  induction s using Multiset.induction_on with
  | empty =>
    intro Q _
    rw [Multiset.map_zero, Multiset.map_zero, Multiset.prod_zero, Multiset.toList_zero, List.nil_append,
      ← C_1, C_apply, evL_monomial, one_mul]
    simp
  | cons t s ih =>
    intro Q hQ
    rw [Multiset.card_cons] at hQ
    have hperm : ((Multiset.map (fun t => ∑ i, M t i • cls i) (t ::ₘ s)).toList ++ Q).Perm
        ((∑ i, M t i • cls i) :: ((Multiset.map (fun t => ∑ i, M t i • cls i) s).toList ++ Q)) := by
      rw [← Multiset.coe_eq_coe, ← Multiset.coe_add, ← Multiset.cons_coe, ← Multiset.coe_add]
      simp only [Multiset.coe_toList, Multiset.map_cons, Multiset.cons_add]
    have hlen : ((Multiset.map (fun t => ∑ i, M t i • cls i) s).toList ++ Q).length + 1 = d := by
      rw [List.length_append, Multiset.length_toList, Multiset.card_map]
      omega
    rw [hp _ _ hperm, hlin _ hlen, Multiset.map_cons, Multiset.prod_cons, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hmid : n (cls i :: ((Multiset.map (fun t => ∑ i, M t i • cls i) s).toList ++ Q)) =
        n ((Multiset.map (fun t => ∑ i, M t i • cls i) s).toList ++ (cls i :: Q)) :=
      hp _ _ List.perm_middle.symm
    have hring : ∀ R : MvPolynomial σ ℝ, C (M t i : ℝ) * X i * R = C (M t i : ℝ) * (R * X i) :=
      fun R => by ring
    rw [hmid, ih (cls i :: Q) (by rw [List.length_cons]; omega), hring, evL_C_mul, evL_mul_X n hp cls _ i Q]

theorem subst_abs [AddCommGroup G] [Fintype σ] (d : ℕ) (n : List G → ℝ)
    (hp : ∀ l l', l.Perm l' → n l = n l')
    (ha : ∀ b b' l, l.length + 1 = d → n ((b + b') :: l) = n (b :: l) + n (b' :: l))
    (cls : σ → G) (M : σ' → σ → ℤ) (H : MvPolynomial σ' ℝ) (m : ℕ) (hH : H.IsHomogeneous m)
    (Q : List G) (hQ : m + Q.length = d) :
    (∑ μ ∈ H.support, H.coeff μ * n ((μ.toMultiset.map fun t => ∑ i, M t i • cls i).toList ++ Q)) =
      evL (fun μ => n ((μ.toMultiset.map cls).toList ++ Q))
        (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H) := by
  conv_rhs => rw [H.as_sum]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl (fun μ hμ => ?_)
  have hdeg : Multiset.card μ.toMultiset = m := by
    have h := hH (mem_support_iff.mp hμ)
    rw [← h]
    simp [Finsupp.card_toMultiset, Finsupp.weight_apply, Finsupp.sum]
  rw [aeval_monomial, algebraMap_eq, evL_C_mul, ← prod_map_toMultiset,
    ← subst_multiset d n hp ha cls M μ.toMultiset Q (by rw [hdeg]; exact hQ)]

end

end BaseChangeColon
