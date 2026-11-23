import Development.DiscreteGroups.GlobalIrreducibility.DzStickDefs

noncomputable section

namespace DiscreteGroups.sglob.Stick

open IsDedekindDomain

theorem associated_prime_pow {A : Type*} [CommRing A] [IsDomain A] {p : ℕ} (hp : p.Prime) {ζ : A}
    (hζ : IsPrimitiveRoot ζ p) : Associated (p : A) ((ζ - 1) ^ (p - 1)) := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  symm
  rw [← Polynomial.eval_one_cyclotomic_prime (R := A) (p := p),
    Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [← Nat.totient_prime hp, ← hζ.card_primitiveRoots, ← Finset.prod_const]
  refine Associated.prod _ _ _ fun η hη ↦ ?_
  obtain ⟨i, -, hi, rfl⟩ := hζ.isPrimitiveRoot_iff.mp (isPrimitiveRoot_of_mem_primitiveRoots hη)
  simpa using (hζ.associated_sub_one_pow_sub_one_of_coprime hi).neg_right

theorem psi_apply (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [Algebra (ZMod p) k] {A : Type*}
    [CommRing A] (ζ : A) (hζ : ζ ^ p = 1) (x : k) :
    psi p k ζ hζ x = ζ ^ (Algebra.trace (ZMod p) k x).val := by
  simp [psi, AddChar.zmodChar_apply]

theorem psi_isPrimitive (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [Finite k] [Algebra (ZMod p) k]
    {A : Type*} [CommRing A] [IsDomain A] (ζ : A) (hζ : IsPrimitiveRoot ζ p) :
    (psi p k ζ hζ.pow_eq_one).IsPrimitive := by
  apply AddChar.IsPrimitive.of_ne_one
  obtain ⟨a, ha⟩ := Algebra.trace_surjective (ZMod p) k 1
  refine AddChar.ne_one_iff.2 ⟨a, fun hf => ?_⟩
  rw [psi_apply, ha, ZMod.val_one, pow_one] at hf
  exact hζ.ne_one (Fact.out : p.Prime).one_lt hf

theorem psi_pow (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [Finite k] [Algebra (ZMod p) k]
    {A : Type*} [CommRing A] (ζ : A) (hζ : ζ ^ p = 1) (x : k) :
    psi p k ζ hζ (x ^ p) = psi p k ζ hζ x := by
  have : CharP k p := charP_of_injective_algebraMap' (ZMod p) p
  have : ExpChar k p := .prime Fact.out
  rw [psi_apply, psi_apply]
  have h := Algebra.trace_eq_of_algEquiv (FiniteField.frobeniusAlgEquiv (ZMod p) k p) x
  have h2 : FiniteField.frobeniusAlgEquiv (ZMod p) k p x = x ^ p := by
    simp [FiniteField.frobeniusAlgEquiv_apply, ZMod.card]
  rw [h2] at h
  rw [h]

namespace GSDatum

variable {p f : ℕ} [Fact p.Prime] {k : Type*} [Field k] [Fintype k] [Algebra (ZMod p) k]
  {A : Type*} [CommRing A] [IsDedekindDomain A] {Q : HeightOneSpectrum A}
  (D : GSDatum p f k A Q)

include D in

theorem p_mem : (p : A) ∈ Q.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← map_natCast D.ι,
    ← map_natCast (algebraMap (ZMod p) k), ZMod.natCast_self, map_zero, map_zero]

theorem ζ_sub_one_mem : D.ζ - 1 ∈ Q.asIdeal := by
  have hp : p.Prime := Fact.out
  obtain ⟨u, hu⟩ := (associated_prime_pow hp D.prim)
  have h : (D.ζ - 1) ^ (p - 1) ∈ Q.asIdeal := by
    rw [← hu]
    exact Ideal.mul_mem_right _ _ (p_mem D)
  exact Q.isPrime.mem_of_pow_mem _ h

theorem val_p : Q.intValuation (p : A) = Q.intValuation (D.ζ - 1) ^ (p - 1) := by
  have hp : p.Prime := Fact.out
  obtain ⟨u, hu⟩ := (associated_prime_pow hp D.prim)
  have h1 : Q.intValuation (u : A) = 1 := by
    rw [HeightOneSpectrum.intValuation_eq_one_iff]
    intro h
    exact Q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h u.isUnit)
  rw [← map_pow, ← hu, map_mul, h1, mul_one]

theorem val_ζ_sub_one_ne_zero : Q.intValuation (D.ζ - 1) ≠ 0 := by
  have hp : p.Prime := Fact.out
  exact Q.intValuation_ne_zero _ (sub_ne_zero.2 (D.prim.ne_one hp.one_lt))

theorem ω_pow_card : D.ω ^ (p ^ f - 1) = 1 := by
  classical
  rw [← D.card_eq, ← Fintype.card_units]
  exact D.ω.pow_card_eq_one

theorem ω_pow_ne_one {a : ℕ} (h0 : 0 < a) (ha : a < p ^ f - 1) : D.ω ^ a ≠ 1 := by
  classical
  intro h
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := kˣ)
  have hord : orderOf x = p ^ f - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hx, Nat.card_eq_fintype_card, Fintype.card_units,
      D.card_eq]
  have h1 : (D.ω ^ a) (x : k) = 1 := by rw [h, MulChar.one_apply_coe]
  rw [MulChar.pow_apply_coe, ← map_pow] at h1
  have h2 : D.ι ((x : k) ^ a) = D.ι 1 := by
    rw [← D.mk_ω, h1, map_one, map_one]
  have h3 : (x : k) ^ a = 1 := D.ι.injective h2
  have h4 : x ^ a = 1 := by
    ext; simpa using h3
  have := Nat.le_of_dvd h0 (orderOf_dvd_of_pow_eq_one h4)
  omega

theorem g_zero : D.g 0 = -1 := by
  have hprim : D.ψ.IsPrimitive := psi_isPrimitive p k D.ζ D.prim
  have hne : D.ψ ≠ 1 := by
    have := hprim (a := 1) one_ne_zero
    rwa [AddChar.mulShift_one] at this
  unfold GSDatum.g
  rw [pow_zero, inv_one]
  exact gaussSum_one_left hne

end GSDatum

end DiscreteGroups.sglob.Stick
