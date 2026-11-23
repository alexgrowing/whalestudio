import Mathlib
open Polynomial

namespace GlobalTheory.CompanionTheory.SubsetSum

noncomputable def subsetPoly {R : Type*} [CommRing R] (r : ℕ) (M : Multiset R) : R[X] :=
  ((M.powersetCard r).map fun S => X - C S.sum).prod

theorem subsetPoly_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (r : ℕ)
    (M : Multiset R) : (subsetPoly r M).map f = subsetPoly r (M.map f) := by
  unfold subsetPoly
  rw [Polynomial.map_multiset_prod, Multiset.powersetCard_map, Multiset.map_map, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro S _
  have h : f S.sum = (S.map f).sum := map_multiset_sum f S
  simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, h]

theorem eval_subsetPoly {R : Type*} [CommRing R] (r : ℕ) (M : Multiset R) (a : R) :
    (subsetPoly r M).eval a = ((M.powersetCard r).map fun S => a - S.sum).prod := by
  unfold subsetPoly
  rw [Polynomial.eval_multiset_prod, Multiset.map_map]
  simp

noncomputable def evalCoef {R : Type*} [CommRing R] (n : ℕ) (P : R[X]) :
    MvPolynomial (Fin n) ℤ →+* R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R) fun j => P.coeff (n - (j + 1))

theorem evalCoef_comp {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) (P : R[X]) :
    f.comp (evalCoef n P) = evalCoef n (P.map f) := by
  apply MvPolynomial.ringHom_ext
  · intro k; simp [evalCoef]
  · intro j; simp [evalCoef, coeff_map]

theorem exists_fin_enum {R : Type*} (M : Multiset R) (n : ℕ) (h : Multiset.card M = n) :
    ∃ x : Fin n → R, Finset.univ.val.map x = M := by
  obtain ⟨l, rfl⟩ := Quot.exists_rep M
  have h' : l.length = n := h
  subst h'
  refine ⟨l.get, ?_⟩
  rw [Fin.univ_val_map, List.ofFn_get]
  rfl

def IsUniv (n r : ℕ) (Φ : (MvPolynomial (Fin n) ℤ)[X]) : Prop :=
  ∀ (R : Type) [CommRing R] (M : Multiset R), Multiset.card M = n →
    Φ.map (evalCoef n (M.map fun x => X + C x).prod) = subsetPoly r M

theorem exists_isUniv (n r : ℕ) : ∃ Φ, IsUniv n r Φ := by
  classical
  let M₀ : Multiset (MvPolynomial (Fin n) ℤ) := Finset.univ.val.map MvPolynomial.X
  let f : MvPolynomial (Fin n) ℤ →+* MvPolynomial (Fin n) ℤ :=
    (MvPolynomial.aeval fun i : Fin n => MvPolynomial.esymm (Fin n) ℤ (i + 1)).toRingHom
  have hsym : ∀ k, (subsetPoly r M₀).coeff k ∈ Set.range f := by
    intro k
    have hs : ((subsetPoly r M₀).coeff k).IsSymmetric := by
      intro e
      have hM : M₀.map (MvPolynomial.rename e : _ →ₐ[ℤ] _).toRingHom = M₀ := by
        have : M₀ = (Finset.univ.val.map e).map MvPolynomial.X := by
          rw [Multiset.map_univ_val_equiv]
        conv_rhs => rw [this]
        simp only [M₀, Multiset.map_map]
        apply Multiset.map_congr rfl
        intro i _
        simp
      have := subsetPoly_map (MvPolynomial.rename e : _ →ₐ[ℤ] _).toRingHom r M₀
      rw [hM] at this
      conv_rhs => rw [← this]
      rw [coeff_map]
      rfl
    obtain ⟨q, hq⟩ := (MvPolynomial.esymmAlgEquiv (Fin n) ℤ (Fintype.card_fin n)).surjective
      ⟨_, hs⟩
    refine ⟨q, ?_⟩
    have := congrArg Subtype.val hq
    exact (MvPolynomial.esymmAlgHom_apply q).symm.trans this
  obtain ⟨Φ, hΦ⟩ := (mem_lifts _).1 ((lifts_iff_coeff_lifts _).2 hsym)
  refine ⟨Φ, ?_⟩
  intro R _ M hM
  obtain ⟨x, rfl⟩ := exists_fin_enum M n hM
  let g : MvPolynomial (Fin n) ℤ →+* R := (MvPolynomial.aeval x : _ →ₐ[ℤ] R).toRingHom
  have h1 : M₀.map g = Finset.univ.val.map x := by
    simp only [M₀, Multiset.map_map]
    apply Multiset.map_congr rfl
    intro i _
    simp [g]
  have h2 : g.comp f = evalCoef n ((Finset.univ.val.map x).map fun x => X + C x).prod := by
    apply MvPolynomial.ringHom_ext
    · intro k; simp [evalCoef]
    · intro j
      have hj := j.2
      have hcard : Multiset.card (Finset.univ.val.map x) = n := hM
      simp only [RingHom.comp_apply, evalCoef, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
      rw [Multiset.prod_X_add_C_coeff _ (by omega), hcard,
        show n - (n - ((j : ℕ) + 1)) = j + 1 by omega]
      simp [f, g, MvPolynomial.aeval_esymm_eq_multiset_esymm]
  rw [← h2, ← Polynomial.map_map, hΦ, subsetPoly_map, h1]

theorem natDegree_prod_X_add_C {R : Type*} [CommRing R] [Nontrivial R] (M : Multiset R) :
    ((M.map fun x => X + C x).prod).natDegree = Multiset.card M := by
  have h : (M.map fun x => X + C x).prod = ((M.map Neg.neg).map fun x => X - C x).prod := by
    rw [Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro x _
    simp
  rw [h, natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_map]

theorem exists_roots_of_monic {K : Type*} [Field K] [IsAlgClosed K] (P : K[X]) (hP : P.Monic) :
    ∃ α : Multiset K, P = (α.map fun x => X + C x).prod := by
  refine ⟨P.roots.map Neg.neg, ?_⟩
  conv_lhs => rw [(IsAlgClosed.splits P).eq_prod_roots_of_monic hP]
  rw [Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro x _
  simp [sub_eq_add_neg]

theorem esymm_one_eq_sum {R : Type*} [CommRing R] (M : Multiset R) : M.esymm 1 = M.sum := by
  simp [Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map]

theorem eval_field {K : Type*} [Field K] [IsAlgClosed K] (r : ℕ) (hr : 0 < r) (P Q : K[X])
    (hP : P.Monic) (hQ : Q.Monic) (hd : P.natDegree = r) :
    ∃ M : Multiset K, Multiset.card M = r + Q.natDegree ∧
      P * Q = (M.map fun x => X + C x).prod ∧ (subsetPoly r M).eval (P.coeff (r - 1)) = 0 := by
  obtain ⟨α, hα⟩ := exists_roots_of_monic P hP
  obtain ⟨β, hβ⟩ := exists_roots_of_monic Q hQ
  have hαc : Multiset.card α = r := by rw [← hd, hα, natDegree_prod_X_add_C]
  have hβc : Multiset.card β = Q.natDegree := by rw [hβ, natDegree_prod_X_add_C]
  refine ⟨α + β, by rw [Multiset.card_add, hαc, hβc], ?_, ?_⟩
  · rw [Multiset.map_add, Multiset.prod_add, ← hα, ← hβ]
  · have hc : P.coeff (r - 1) = α.sum := by
      rw [hα, Multiset.prod_X_add_C_coeff _ (by omega), hαc, show r - (r - 1) = 1 by omega,
        esymm_one_eq_sum]
    rw [eval_subsetPoly, hc]
    apply Multiset.prod_eq_zero
    rw [Multiset.mem_map]
    exact ⟨α, Multiset.mem_powersetCard.2 ⟨Multiset.le_add_right _ _, hαc⟩, sub_self _⟩

theorem eval_domain {U : Type} [CommRing U] [IsDomain U] (r : ℕ) (hr : 0 < r) (P Q : U[X])
    (hP : P.Monic) (hQ : Q.Monic) (hd : P.natDegree = r) {n : ℕ} (hn : n = r + Q.natDegree) {Φ} (hΦ : IsUniv n r Φ) :
    (Φ.map (evalCoef n (P * Q))).eval (P.coeff (r - 1)) = 0 := by
  let K := AlgebraicClosure (FractionRing U)
  let ι : U →+* K := (algebraMap (FractionRing U) K).comp (algebraMap U (FractionRing U))
  have hι : Function.Injective ι :=
    (algebraMap (FractionRing U) K).injective.comp (IsFractionRing.injective U (FractionRing U))
  have hdQ : (Q.map ι).natDegree = Q.natDegree := hQ.natDegree_map ι
  obtain ⟨M, hc, hM, he⟩ := eval_field r hr (P.map ι) (Q.map ι) (hP.map ι) (hQ.map ι)
    (by rw [hP.natDegree_map ι, hd])
  apply hι
  rw [map_zero, ← eval_map_apply, Polynomial.map_map, evalCoef_comp, Polynomial.map_mul, hM,
    ← coeff_map, hΦ K M (by rw [hc, hdQ, hn])]
  exact he

noncomputable def gen {S : Type*} [CommRing S] (d : ℕ) (c : Fin d → S) : Polynomial S :=
  Polynomial.X ^ d + ∑ i : Fin d, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)

theorem gen_monic {S : Type*} [CommRing S] (d : ℕ) (c : Fin d → S) : (gen d c).Monic :=
  monic_X_pow_add (degree_sum_fin_lt c)

theorem gen_natDegree {S : Type*} [CommRing S] [Nontrivial S] (d : ℕ) (c : Fin d → S) :
    (gen d c).natDegree = d := by
  rw [gen, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  exact degree_sum_fin_lt c

theorem gen_map {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T) (d : ℕ) (c : Fin d → S) :
    (gen d c).map f = gen d (fun i => f (c i)) := by
  simp [gen, Polynomial.map_sum]

theorem eq_gen {T : Type*} [CommRing T] (P : T[X]) (hP : P.Monic) (d : ℕ) (hd : P.natDegree = d) :
    P = gen d (fun i => P.coeff i) := by
  subst hd
  conv_lhs => rw [hP.as_sum]
  rw [gen, Fin.sum_univ_eq_sum_range (fun i => C (P.coeff i) * X ^ i)]

theorem prod_sub_subset_sum_eq_zero (R : Type) [CommRing R] (r : ℕ) (m : Multiset R) (A B : R[X])
    (hr : 0 < r) (hA : A.Monic) (hB : B.Monic) (hd : A.natDegree = r)
    (h : A * B = (m.map fun x => X + C x).prod) :
    ((m.powersetCard r).map fun S => A.coeff (r - 1) - S.sum).prod = 0 := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  have hm : Multiset.card m = r + B.natDegree := by
    rw [← natDegree_prod_X_add_C, ← h, hA.natDegree_mul hB, hd]
  obtain ⟨Φ, hΦ⟩ := exists_isUniv (r + B.natDegree) r
  let U := MvPolynomial (Fin r ⊕ Fin B.natDegree) ℤ
  let g : U →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R)
    (Sum.elim (fun i => A.coeff i) (fun j => B.coeff j))
  let A₀ : U[X] := gen r fun i => MvPolynomial.X (Sum.inl i)
  let B₀ : U[X] := gen B.natDegree fun j => MvPolynomial.X (Sum.inr j)
  have hA₀ : A₀.map g = A :=
    (gen_map _ _ _).trans ((congrArg (gen r) (funext fun i => MvPolynomial.eval₂_X _ _ _)).trans
      (eq_gen A hA r hd).symm)
  have hB₀ : B₀.map g = B :=
    (gen_map _ _ _).trans ((congrArg (gen _) (funext fun j => MvPolynomial.eval₂_X _ _ _)).trans
      (eq_gen B hB _ rfl).symm)
  have hBd : B₀.natDegree = B.natDegree := gen_natDegree _ _
  have key := eval_domain r hr A₀ B₀ (gen_monic _ _) (gen_monic _ _) (gen_natDegree _ _)
    (by rw [hBd]) hΦ
  have := congrArg g key
  rw [map_zero, ← eval_map_apply, Polynomial.map_map, evalCoef_comp, Polynomial.map_mul, hA₀, hB₀,
    ← coeff_map, hA₀, h, hΦ R m hm, eval_subsetPoly] at this
  exact this

theorem prod_sub_subset_sum_eq_zero_complex (R : Type) [CommRing R] [Algebra ℂ R] (r : ℕ)
    (m : Multiset ℂ) (A B : R[X]) (hr : 0 < r) (hA : A.Monic) (hB : B.Monic)
    (hd : A.natDegree = r)
    (h : A * B = (m.map fun x => X + C (algebraMap ℂ R x)).prod) :
    ((m.powersetCard r).map fun S => A.coeff (r - 1) - algebraMap ℂ R S.sum).prod = 0 := by
  have key := prod_sub_subset_sum_eq_zero R r (m.map (algebraMap ℂ R)) A B hr hA hB hd
    (by rw [Multiset.map_map]; exact h)
  rw [Multiset.powersetCard_map, Multiset.map_map] at key
  rw [← key]
  congr 1
  apply Multiset.map_congr rfl
  intro S _
  simp [map_multiset_sum]

end GlobalTheory.CompanionTheory.SubsetSum
