import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private noncomputable def tchU (n : ℕ) (O : Type) [CommRing O] (i : Fin n) : (MvPowerSeries (Fin n) O)ˣ :=
  (show IsUnit (1 + MvPowerSeries.X i : MvPowerSeries (Fin n) O) from
    MvPowerSeries.isUnit_iff_constantCoeff.2 (by simp)).unit

private lemma tchU_val (n : ℕ) (O : Type) [CommRing O] (i : Fin n) :
    (tchU n O i : MvPowerSeries (Fin n) O) = 1 + MvPowerSeries.X i := IsUnit.unit_spec _

private lemma tch_poly (n : ℕ) (R : Type) [CommRing R] {X : Type} (s : Finset X) (x : X → R)
    (e : X → Fin n →₀ ℕ) (he : Set.InjOn e s)
    (h : ∑ j ∈ s, (∏ i, (1 + MvPowerSeries.X i : MvPowerSeries (Fin n) R) ^ (e j i)) * C (x j) = 0) :
    ∀ j ∈ s, x j = 0 := by
  classical
  have h1 : (∑ j ∈ s, (∏ i, (1 + MvPolynomial.X i : MvPolynomial (Fin n) R) ^ (e j i)) *
      MvPolynomial.C (x j)) = 0 := by
    apply MvPolynomial.coe_injective (Fin n) R
    rw [MvPolynomial.coe_zero, ← h, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_prod]
    simp
  have h2 := congrArg (MvPolynomial.aeval (R := R)
    (fun i : Fin n => (MvPolynomial.X i - 1 : MvPolynomial (Fin n) R))) h1
  rw [map_sum, map_zero] at h2
  have h3 : ∑ j ∈ s, MvPolynomial.monomial (e j) (x j) = 0 := by
    rw [← h2]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
    simp [map_prod, mul_comm]
  intro j hj
  have h4 := congrArg (MvPolynomial.coeff (e j)) h3
  rw [MvPolynomial.coeff_sum, Finset.sum_eq_single j] at h4
  · simpa using h4
  · intro k hk hkj
    rw [MvPolynomial.coeff_monomial, if_neg]
    intro hh
    exact hkj (he hk hj hh)
  · intro h; exact absurd hj h

theorem UpperTheory.V.Alg.tchar :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X], ∃ (n : ℕ) (t : Multiplicative X →* (MvPowerSeries (Fin n) O)ˣ), (∀ j, constantCoeff (t j : MvPowerSeries (Fin n) O) = 1) ∧
      ∀ (R : Type) [CommRing R] [Algebra O R] (s : Finset X) (x : X → R),
        ∑ j ∈ s, MvPowerSeries.map (algebraMap O R) (t (Multiplicative.ofAdd j) : MvPowerSeries (Fin n) O) * C (x j) = 0 → ∀ j ∈ s, x j = 0 := by
  intro O _ _ X _ _ _
  classical
  let n := Module.finrank ℤ X
  let b : Module.Basis (Fin n) ℤ X := Module.finBasis ℤ X
  let t : Multiplicative X →* (MvPowerSeries (Fin n) O)ˣ :=
    { toFun := fun j => ∏ i, tchU n O i ^ (b.repr j.toAdd i)
      map_one' := by simp
      map_mul' := by
        intro a c
        simp [zpow_add, Finset.prod_mul_distrib] }
  have ht : ∀ j : X, t (Multiplicative.ofAdd j) = ∏ i, tchU n O i ^ (b.repr j i) := fun j => rfl
  refine ⟨n, t, ?_, ?_⟩
  · intro j
    have h1 : ∀ i, Units.map (constantCoeff : MvPowerSeries (Fin n) O →+* O).toMonoidHom (tchU n O i) = 1 := by
      intro i
      ext
      simp [tchU_val]
    have h2 : Units.map (constantCoeff : MvPowerSeries (Fin n) O →+* O).toMonoidHom (t j) = 1 := by
      have := ht j.toAdd
      rw [ofAdd_toAdd] at this
      rw [this, map_prod]
      simp only [map_zpow, h1, one_zpow, Finset.prod_const_one]
    simpa using congrArg Units.val h2
  · intro R _ _ s x h
    let N : ℕ := ∑ j ∈ s, ∑ i, (b.repr j i).natAbs
    have hN : ∀ j ∈ s, ∀ i, 0 ≤ b.repr j i + N := by
      intro j hj i
      have h1 : (b.repr j i).natAbs ≤ ∑ i, (b.repr j i).natAbs :=
        Finset.single_le_sum (f := fun i => (b.repr j i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have h2 : ∑ i, (b.repr j i).natAbs ≤ N :=
        Finset.single_le_sum (f := fun j => ∑ i, (b.repr j i).natAbs) (fun _ _ => Nat.zero_le _) hj
      omega
    let e : X → Fin n →₀ ℕ := fun j => Finsupp.equivFunOnFinite.symm fun i => (b.repr j i + N).toNat
    have he : ∀ j i, e j i = (b.repr j i + N).toNat := fun j i => rfl
    refine tch_poly n R s x e ?_ ?_
    · intro j hj k hk hjk
      apply b.repr.injective
      ext i
      have h1 := he j i
      rw [hjk, he] at h1
      have := hN j hj i
      have := hN k hk i
      omega
    · have h1 := congrArg (fun y => MvPowerSeries.map (algebraMap O R)
        ((∏ i, tchU n O i ^ (N : ℤ) : (MvPowerSeries (Fin n) O)ˣ) : MvPowerSeries (Fin n) O) * y) h
      simp only [mul_zero] at h1
      rw [Finset.mul_sum] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [← mul_assoc, ← map_mul, ← Units.val_mul, ht, ← Finset.prod_mul_distrib]
      congr 1
      have h2 : ∀ i, tchU n O i ^ (N : ℤ) * tchU n O i ^ (b.repr j i) = tchU n O i ^ (e j i) := by
        intro i
        rw [← zpow_add, ← zpow_natCast, he, Int.toNat_of_nonneg (hN j hj i), add_comm]
      simp only [h2]
      simp [map_prod, tchU_val]
