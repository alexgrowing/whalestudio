import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
open IsLocalRing UpperTheory.V.Alg

private def Cg {A : Type} [CommRing A] (I : Ideal A) (k : ℕ) (a b : A) : Prop :=
  b ∈ I ^ k ∧ a - b ∈ I ^ (k + 1)

private theorem Cg.mul {A : Type} [CommRing A] {I : Ideal A} {k l : ℕ} {a b c d : A}
    (h1 : Cg I k a b) (h2 : Cg I l c d) : Cg I (k + l) (a * c) (b * d) := by
  have hc : c ∈ I ^ l := by
    have := (I ^ l).add_mem (Ideal.pow_le_pow_right (Nat.le_succ l) h2.2) h2.1
    simpa using this
  refine ⟨by rw [pow_add]; exact Ideal.mul_mem_mul h1.1 h2.1, ?_⟩
  have e : a * c - b * d = (a - b) * c + b * (c - d) := by ring
  rw [e]
  refine Ideal.add_mem _ ?_ ?_
  · rw [show k + l + 1 = (k + 1) + l by ring, pow_add]
    exact Ideal.mul_mem_mul h1.2 hc
  · rw [add_assoc, pow_add]
    exact Ideal.mul_mem_mul h1.1 h2.2

private theorem Cg.refl {A : Type} [CommRing A] (I : Ideal A) (a : A) : Cg I 0 a a :=
  ⟨by simp, by simp⟩

private theorem Cg.pow {A : Type} [CommRing A] {I : Ideal A} {a b : A}
    (h : Cg I 1 a b) (k : ℕ) : Cg I k (a ^ k) (b ^ k) := by
  induction k with
  | zero => simpa using Cg.refl I 1
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul h

private theorem Cg.prod {A ι : Type} [CommRing A] {I : Ideal A} {a b : ι → A}
    (h : ∀ i, Cg I 1 (a i) (b i)) (d : ι → ℕ) (s : Finset ι) :
    Cg I (∑ i ∈ s, d i) (∏ i ∈ s, a i ^ d i) (∏ i ∈ s, b i ^ d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Cg.refl I 1
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, Finset.prod_insert hi]
    exact ((h i).pow _).mul ih

private theorem order_of_mem_pow {σ E : Type} [Field E] (k : ℕ) :
    ∀ f : MvPowerSeries σ E, f ∈ maximalIdeal (MvPowerSeries σ E) ^ k → (k : ℕ∞) ≤ f.order := by
  induction k with
  | zero => intro f _; simp
  | succ k ih =>
    intro f hf
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on hf ?_ ?_
    · intro a ha b hb
      have h1 : ((1 : ℕ) : ℕ∞) ≤ b.order := by
        refine MvPowerSeries.nat_le_order ?_
        intro d hd
        have hd0 : d = 0 := by
          have : Finsupp.degree d = 0 := by omega
          exact (Finsupp.degree_eq_zero_iff d).1 this
        subst hd0
        rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
          isUnit_iff_ne_zero, not_not] at hb
        simpa using hb
      refine le_trans ?_ MvPowerSeries.le_order_mul
      rw [Nat.cast_add]
      exact add_le_add (ih a ha) h1
    · intro a b ha hb
      exact le_trans (le_min ha hb) MvPowerSeries.min_order_le_add

theorem UpperTheory.eq_zero_of_homogeneous_aeval_mem_maximalIdeal_pow_succ :
    ∀ (O E : Type) [CommRing O] [IsDomain O] [Field E] [Algebra O E] [IsFractionRing O E] (n : ℕ) (u : Fin n → MvPowerSeries (Fin n) E) (c : O), c ≠ 0 → (∀ i, u i - c • MvPowerSeries.X i ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ 2) → ∀ (N : ℕ) (h : MvPolynomial (Fin n) O), h.IsHomogeneous N → MvPolynomial.aeval u h ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ (N + 1) → h = 0 := by
  intro O E _ _ _ _ _ n u c hc hu N h hh hm
  classical
  set I := maximalIdeal (MvPowerSeries (Fin n) E) with hI
  let v : Fin n → MvPowerSeries (Fin n) E := fun i => c • MvPowerSeries.X i
  have hv : ∀ i, Cg I 1 (u i) (v i) := by
    intro i
    refine ⟨?_, hu i⟩
    rw [pow_one]
    have hX : (MvPowerSeries.X i : MvPowerSeries (Fin n) E) ∈ I := by
      rw [hI, mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
      simp
    show c • MvPowerSeries.X i ∈ I
    rw [Algebra.smul_def]
    exact I.mul_mem_left _ hX
  have hdeg : ∀ d ∈ h.support, ∑ i, d i = N := by
    intro d hd
    have := hh (MvPolynomial.mem_support_iff.1 hd)
    rw [← this, ← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]
    rfl
  have hdiff : MvPolynomial.aeval u h - MvPolynomial.aeval v h ∈ I ^ (N + 1) := by
    rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq',
      MvPolynomial.eval₂_eq', ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun d hd => ?_
    rw [← mul_sub]
    refine Ideal.mul_mem_left _ _ ?_
    have := (Cg.prod hv d Finset.univ).2
    rwa [hdeg d hd] at this
  have hvm : MvPolynomial.aeval v h ∈ I ^ (N + 1) := by
    have := (I ^ (N + 1)).sub_mem hm hdiff
    simpa using this
  have hval : MvPolynomial.aeval v h =
      ∑ d ∈ h.support, MvPowerSeries.monomial d (algebraMap O E (h.coeff d * c ^ N)) := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
    refine Finset.sum_congr rfl fun d hd => ?_
    have hX : (∏ i, (MvPowerSeries.X i : MvPowerSeries (Fin n) E) ^ d i)
        = MvPowerSeries.monomial d 1 := by
      have h1 : ((MvPolynomial.monomial d (1 : E) : MvPolynomial (Fin n) E) :
          MvPowerSeries (Fin n) E) = MvPowerSeries.monomial d 1 := MvPolynomial.coe_monomial _ _
      rw [← h1, MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
      rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply]
      simp [map_prod]
    simp only [v, Algebra.smul_def, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    rw [hdeg d hd, hX, ← mul_assoc, ← map_pow, ← map_mul, MvPowerSeries.algebraMap_apply,
      ← MvPowerSeries.monomial_zero_eq_C_apply, MvPowerSeries.monomial_mul_monomial]
    simp
  by_contra hne
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.2 hne
  have h0 : MvPowerSeries.coeff d (MvPolynomial.aeval v h) = 0 := by
    refine MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le ?_ (order_of_mem_pow _ _ hvm))
    rw [Finsupp.degree_eq_sum, hdeg d hd]
    exact_mod_cast Nat.lt_succ_self N
  rw [hval, map_sum, Finset.sum_eq_single d] at h0
  · rw [MvPowerSeries.coeff_monomial_same,
      map_eq_zero_iff _ (IsFractionRing.injective O E)] at h0
    exact mul_ne_zero (MvPolynomial.mem_support_iff.1 hd) (pow_ne_zero _ hc) h0
  · intro e _ he
    exact MvPowerSeries.coeff_monomial_ne he.symm _
  · intro h'; exact absurd hd h'
