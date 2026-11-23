import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic

set_option autoImplicit false

noncomputable section

open MvPolynomial Finset GlobalTheory.Cris GlobalTheory.LatJet
open scoped Classical

namespace GlobalTheory.DivPowTrunc

variable (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Type) [Fintype I] (n : ℕ)

abbrev K : Type := FractionRing R

theorem charZero_K : CharZero (K R) :=
  charZero_of_injective_algebraMap (IsFractionRing.injective R (K R))

attribute [local instance] charZero_K

variable {R I} in

def filt (k : ℕ) : Ideal (MvPolynomial I (K R)) where
  carrier := {p | ∀ μ : I →₀ ℕ, ∑ i, μ i < k → p.coeff μ = 0}
  zero_mem' := by intro μ _; simp
  add_mem' := by
    intro p q hp hq μ hμ
    simp [coeff_add, hp μ hμ, hq μ hμ]
  smul_mem' := by
    intro c p hp μ hμ
    rw [smul_eq_mul, coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have : ∑ i, x.2 i ≤ ∑ i, μ i := by
      rw [← hx]; simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib]; omega
    rw [hp x.2 (lt_of_le_of_lt this hμ), mul_zero]

theorem filt_mul {a b : ℕ} {p q : MvPolynomial I (K R)} (hp : p ∈ filt a) (hq : q ∈ filt b) :
    p * q ∈ filt (a + b) := by
  intro μ hμ
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have hs : ∑ i, x.1 i + ∑ i, x.2 i = ∑ i, μ i := by
    rw [← hx]; simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib]
  by_cases h1 : ∑ i, x.1 i < a
  · rw [hp x.1 h1, zero_mul]
  · rw [hq x.2 (by omega), mul_zero]

theorem filt_pow (k : ℕ) : (filt (R := R) (I := I) 1) ^ k ≤ filt k := by
  induction k with
  | zero => intro p _ μ hμ; omega
  | succ k ih =>
    rw [pow_succ, Ideal.mul_le]
    intro p hp q hq
    exact filt_mul R I (ih hp) hq

abbrev C : Type := MvPolynomial I (K R) ⧸ (filt (R := R) (I := I) (n + 2))

def m : Ideal (C R I n) := (filt 1).map (Ideal.Quotient.mk _)

theorem m_pow : m R I n ^ (n + 2) = ⊥ := by
  rw [m, ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  exact filt_pow R I _

def δ : DividedPowers (m R I n) := DividedPowers.RatAlgebra.dividedPowers _

def x (i : I) : C R I n := Ideal.Quotient.mk _ (X i)

theorem x_mem (i : I) : x R I n i ∈ m R I n := by
  refine Ideal.mem_map_of_mem _ ?_
  intro μ hμ
  have : μ ≠ Finsupp.single i 1 := by
    rintro rfl; simp at hμ
  rw [coeff_X']; simp [Ne.symm this]

def E (ν : I → ℕ) : C R I n := ∏ i, (δ R I n).dpow (ν i) (x R I n i)

theorem dpow_mem_pow (k : ℕ) {z : C R I n} (hz : z ∈ m R I n) : (δ R I n).dpow k z ∈ m R I n ^ k := by
  simp only [δ, DividedPowers.RatAlgebra.dpow_apply, if_pos hz]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hz k)

theorem E_big (ν : I → ℕ) (h : n + 2 ≤ ∑ i, ν i) : E R I n ν = 0 := by
  have h1 : E R I n ν ∈ m R I n ^ (∑ i, ν i) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun i _ => dpow_mem_pow R I n _ (x_mem R I n i)
  have h2 := Ideal.pow_le_pow_right h h1
  rw [m_pow] at h2
  exact (Ideal.mem_bot).1 h2

theorem E_mul (ν ν' : I → ℕ) : E R I n ν * E R I n ν' =
    (∏ i, (ν i + ν' i).choose (ν i) : ℕ) • E R I n (ν + ν') := by
  rw [E, E, E, ← Finset.prod_mul_distrib, nsmul_eq_mul, Nat.cast_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [(δ R I n).mul_dpow (x_mem R I n i)]; rfl

theorem E_zero : E R I n 0 = 1 := by
  simp [E, (δ R I n).dpow_zero (x_mem R I n _)]

end GlobalTheory.DivPowTrunc

namespace GlobalTheory.DivPowTrunc

variable (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Type) [Fintype I] (n : ℕ)

attribute [local instance] charZero_K

theorem mk_C (c : K R) : Ideal.Quotient.mk (filt (R := R) (I := I) (n + 2)) (MvPolynomial.C c) = algebraMap (K R) (C R I n) c := by
  rw [← MvPolynomial.algebraMap_eq]; exact Ideal.Quotient.mk_algebraMap _ _ _

theorem E_eq (ν : I → ℕ) : E R I n ν = Ideal.Quotient.mk _
    (monomial (Finsupp.equivFunOnFinite.symm ν) (∏ i, ((ν i).factorial : K R))⁻¹) := by
  have h1 : (∏ i, ((ν i).factorial : C R I n)) * E R I n ν =
      Ideal.Quotient.mk _ (monomial (Finsupp.equivFunOnFinite.symm ν) (1 : K R)) := by
    rw [E, ← Finset.prod_mul_distrib]
    simp_rw [(δ R I n).factorial_mul_dpow_eq_pow (x_mem R I n _), x, ← map_pow, ← map_prod]
    congr 1
    rw [← prod_X_pow_eq_monomial]
    symm
    refine Finset.prod_subset (Finset.subset_univ _) fun i _ hi => ?_
    rw [Finsupp.mem_support_iff, not_not] at hi
    rw [hi, pow_zero]
  have h2 : (∏ i, ((ν i).factorial : C R I n)) = algebraMap (K R) (C R I n) (∏ i, ((ν i).factorial : K R)) := by
    simp [map_prod, map_natCast]
  have hne : (∏ i, ((ν i).factorial : K R)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  rw [show monomial (Finsupp.equivFunOnFinite.symm ν) (∏ i, ((ν i).factorial : K R))⁻¹ =
      MvPolynomial.C (∏ i, ((ν i).factorial : K R))⁻¹ * monomial (Finsupp.equivFunOnFinite.symm ν) 1 by
    rw [C_mul_monomial, mul_one], map_mul, ← h1, h2, ← mul_assoc, mk_C, ← map_mul, inv_mul_cancel₀ hne, map_one,
    one_mul]

def Eidx (ν : Idx I n) : C R I n := E R I n ν.1

def S : Submodule R (C R I n) := Submodule.span R (Set.range (Eidx R I n))

theorem E_mem_S (μ : I → ℕ) : E R I n μ ∈ S R I n := by
  by_cases h : ∑ i, μ i ≤ n + 1
  · exact Submodule.subset_span ⟨⟨μ, h⟩, rfl⟩
  · rw [E_big R I n μ (by omega)]; exact Submodule.zero_mem _

theorem S_mul {a b : C R I n} (ha : a ∈ S R I n) (hb : b ∈ S R I n) : a * b ∈ S R I n := by
  have : S R I n * S R I n ≤ S R I n := by
    rw [S, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨a, ⟨ν, rfl⟩, b, ⟨ν', rfl⟩, rfl⟩
    dsimp only
    rw [Eidx, Eidx, E_mul]
    exact nsmul_mem (E_mem_S R I n _) _
  exact this (Submodule.mul_mem_mul ha hb)

def B : Subalgebra R (C R I n) :=
  (S R I n).toSubalgebra (by rw [← E_zero R I n]; exact E_mem_S R I n _) fun _ _ ha hb => S_mul R I n ha hb

theorem linIndep : LinearIndependent R (Eidx R I n) := by
  rw [linearIndependent_iff']
  intro s g hg ν hν
  have h3 : ∑ μ ∈ s, g μ • Eidx R I n μ = Ideal.Quotient.mk _ (∑ μ ∈ s,
      monomial (Finsupp.equivFunOnFinite.symm μ.1) (algebraMap R (K R) (g μ) * (∏ i, ((μ.1 i).factorial : K R))⁻¹)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Eidx, E_eq, Algebra.smul_def, IsScalarTower.algebraMap_apply R (K R) (C R I n), ← mk_C, ← map_mul,
      C_mul_monomial]
  rw [h3, Ideal.Quotient.eq_zero_iff_mem] at hg
  have := hg (Finsupp.equivFunOnFinite.symm ν.1) (by have := ν.2; simp; omega)
  rw [coeff_sum, Finset.sum_eq_single ν] at this
  · rw [coeff_monomial, if_pos rfl] at this
    have hne : (∏ i, ((ν.1 i).factorial : K R))⁻¹ ≠ 0 :=
      inv_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
    have h4 : algebraMap R (K R) (g ν) = 0 := (mul_eq_zero.1 this).resolve_right hne
    exact IsFractionRing.injective R (K R) (by rw [h4, map_zero])
  · intro μ _ hμ
    rw [coeff_monomial, if_neg]
    intro h
    exact hμ (Subtype.ext (Finsupp.equivFunOnFinite.symm.injective h))
  · intro h; exact absurd hν h

def v (ν : Idx I n) : B R I n := ⟨Eidx R I n ν, Submodule.subset_span ⟨ν, rfl⟩⟩

theorem span_v : ⊤ ≤ Submodule.span R (Set.range (v R I n)) := by
  rintro ⟨z, hz⟩ -
  change z ∈ S R I n at hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨ν, rfl⟩ := hy
    exact Submodule.subset_span ⟨ν, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add a c ha hc iha ihc => exact Submodule.add_mem _ iha ihc
  | smul r a ha iha => exact Submodule.smul_mem _ r iha

def b : Module.Basis (Idx I n) R (B R I n) :=
  Module.Basis.mk (v := v R I n) (LinearIndependent.of_comp (B R I n).val.toLinearMap (linIndep R I n)) (span_v R I n)

theorem b_apply (ν : Idx I n) : ((b R I n ν : B R I n) : C R I n) = E R I n ν.1 := by
  simp [b, v, Eidx]

end GlobalTheory.DivPowTrunc

namespace GlobalTheory.DivPowTrunc

variable (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Type) [Fintype I] (n : ℕ)

attribute [local instance] charZero_K

theorem cc (p : MvPolynomial I (K R)) : constantCoeff p = coeff 0 p := congrFun constantCoeff_eq p

def εC : C R I n →+* K R :=
  Ideal.Quotient.lift _ MvPolynomial.constantCoeff fun a ha => by
    rw [cc]; exact ha 0 (by simp)

theorem εC_mk (p : MvPolynomial I (K R)) : εC R I n (Ideal.Quotient.mk _ p) = constantCoeff p :=
  Ideal.Quotient.lift_mk _ _ _

theorem εC_alg (c : K R) : εC R I n (algebraMap (K R) (C R I n) c) = c := by
  rw [← mk_C, εC_mk, constantCoeff_C]

theorem εC_m {z : C R I n} (hz : z ∈ m R I n) : εC R I n z = 0 := by
  have : m R I n ≤ RingHom.ker (εC R I n) := by
    rw [m, Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, RingHom.mem_ker, εC_mk, cc]
    exact hp 0 (by simp)
  exact this hz

theorem mem_m {z : C R I n} (hz : εC R I n z = 0) : z ∈ m R I n := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine Ideal.mem_map_of_mem _ ?_
  intro μ hμ
  have : μ = 0 := by
    ext i
    have := (Finset.sum_eq_zero_iff.1 (Nat.lt_one_iff.1 hμ)) i (Finset.mem_univ _)
    simpa using this
  rw [this, ← cc, ← εC_mk]; exact hz

theorem εC_dpow {z : C R I n} (hz : z ∈ m R I n) {k : ℕ} (hk : k ≠ 0) : εC R I n ((δ R I n).dpow k z) = 0 := by
  have := congrArg (εC R I n) ((δ R I n).factorial_mul_dpow_eq_pow (n := k) hz)
  rw [map_mul, map_pow, εC_m R I n hz, zero_pow hk, map_natCast] at this
  exact (mul_eq_zero.1 this).resolve_left (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))

theorem εC_E (ν : I → ℕ) : εC R I n (E R I n ν) = if ν = 0 then 1 else 0 := by
  split_ifs with h
  · rw [h, E_zero, map_one]
  · obtain ⟨i, hi⟩ : ∃ i, ν i ≠ 0 := by
      by_contra h'; push_neg at h'; exact h (funext h')
    rw [E, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (εC_dpow R I n (x_mem R I n i) hi)

def i0 : Idx I n := ⟨0, by simp⟩

def εR : B R I n →ₗ[R] K R where
  toFun y := εC R I n y
  map_add' y z := by simp
  map_smul' r y := by
    change εC R I n ((r • y : B R I n) : C R I n) = r • εC R I n y
    rw [Subalgebra.coe_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply R (K R) (C R I n), map_mul, εC_alg,
      Algebra.smul_def]

theorem coord_eq (y : B R I n) : algebraMap R (K R) ((b R I n).repr y (i0 I n)) = εC R I n y := by
  have : (Algebra.linearMap R (K R)).comp ((b R I n).coord (i0 I n)) = εR R I n := by
    refine (b R I n).ext fun ν => ?_
    simp only [LinearMap.comp_apply, Module.Basis.coord_apply, Module.Basis.repr_self, Algebra.linearMap_apply]
    change _ = εC R I n ((b R I n ν : B R I n) : C R I n)
    rw [b_apply, εC_E, Finsupp.single_apply]
    by_cases h : ν.1 = 0
    · have : i0 I n = ν := Subtype.ext h.symm
      simp [this, h]
    · have : i0 I n ≠ ν := fun e => h (congrArg Subtype.val e).symm
      simp [this, Ne.symm this, h]
  exact LinearMap.congr_fun this y

def π : B R I n →+* R where
  toFun y := (b R I n).repr y (i0 I n)
  map_one' := IsFractionRing.injective R (K R) (by rw [coord_eq]; simp)
  map_mul' y z := IsFractionRing.injective R (K R) (by rw [map_mul (algebraMap R (K R)), coord_eq, coord_eq, coord_eq,
    Subalgebra.coe_mul, map_mul])
  map_zero' := by rw [LinearEquiv.map_zero, Finsupp.zero_apply]
  map_add' y z := by rw [LinearEquiv.map_add, Finsupp.add_apply]

theorem π_apply (y : B R I n) : algebraMap R (K R) (π R I n y) = εC R I n y := coord_eq R I n y

theorem dpow_x_mem (i : I) (k : ℕ) : (δ R I n).dpow k (x R I n i) ∈ B R I n := by
  change _ ∈ S R I n
  by_cases hk : k ≤ n + 1
  · have : (δ R I n).dpow k (x R I n i) = E R I n (Pi.single i k) := by
      rw [E, Finset.prod_eq_single i]
      · simp
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj, (δ R I n).dpow_zero (x_mem R I n j)]
      · simp
    rw [this]; exact E_mem_S R I n _
  · have h1 := Ideal.pow_le_pow_right (show n + 2 ≤ k by omega) (dpow_mem_pow R I n k (x_mem R I n i))
    rw [m_pow, Ideal.mem_bot] at h1
    rw [h1]; exact Submodule.zero_mem _

def Q (z : C R I n) : Prop := z ∈ m R I n ∧ ∀ k, (δ R I n).dpow k z ∈ B R I n

theorem Q_zero : Q R I n 0 := by
  refine ⟨Ideal.zero_mem _, fun k => ?_⟩
  rcases k with _ | k
  · rw [(δ R I n).dpow_zero (Ideal.zero_mem _)]; exact Subalgebra.one_mem _
  · rw [(δ R I n).dpow_eval_zero k.succ_ne_zero]; exact Subalgebra.zero_mem _

theorem Q_add {y z : C R I n} (hy : Q R I n y) (hz : Q R I n z) : Q R I n (y + z) := by
  refine ⟨Ideal.add_mem _ hy.1 hz.1, fun k => ?_⟩
  rw [(δ R I n).dpow_add hy.1 hz.1]
  exact Subalgebra.sum_mem _ fun p _ => Subalgebra.mul_mem _ (hy.2 _) (hz.2 _)

theorem Q_smul (r : R) {z : C R I n} (hz : Q R I n z) : Q R I n (r • z) := by
  rw [Algebra.smul_def]
  refine ⟨Ideal.mul_mem_left _ _ hz.1, fun k => ?_⟩
  rw [(δ R I n).dpow_mul hz.1]
  exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.algebraMap_mem _ r) _) (hz.2 k)

theorem Q_E {ν : I → ℕ} (hν : ν ≠ 0) : Q R I n (E R I n ν) := by
  obtain ⟨i₀, hi⟩ : ∃ i, ν i ≠ 0 := by
    by_contra h'; push_neg at h'; exact hν (funext h')
  have hE : E R I n ν = (∏ i ∈ Finset.univ.erase i₀, (δ R I n).dpow (ν i) (x R I n i)) *
      (δ R I n).dpow (ν i₀) (x R I n i₀) := (Finset.prod_erase_mul _ _ (Finset.mem_univ _)).symm
  have hy : (δ R I n).dpow (ν i₀) (x R I n i₀) ∈ m R I n := (δ R I n).dpow_mem hi (x_mem R I n i₀)
  have ha : (∏ i ∈ Finset.univ.erase i₀, (δ R I n).dpow (ν i) (x R I n i)) ∈ B R I n :=
    Subalgebra.prod_mem _ fun i _ => dpow_x_mem R I n i _
  rw [hE]
  refine ⟨Ideal.mul_mem_left _ _ hy, fun k => ?_⟩
  rw [(δ R I n).dpow_mul hy, (δ R I n).dpow_comp hi (x_mem R I n i₀)]
  exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ ha _)
    (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) (dpow_x_mem R I n i₀ _))

theorem integral (y : B R I n) (hy : π R I n y = 0) : Q R I n (y : C R I n) := by
  rw [← (b R I n).linearCombination_repr y, Finsupp.linearCombination_apply, Finsupp.sum,
    AddSubmonoidClass.coe_finset_sum]
  refine Finset.sum_induction _ (Q R I n) (fun _ _ => Q_add R I n) (Q_zero R I n) fun ν _ => ?_
  rw [Subalgebra.coe_smul, b_apply]
  by_cases hν : ν.1 = 0
  · have : ν = i0 I n := Subtype.ext hν
    have h0 : (b R I n).repr y ν = 0 := by rw [this]; exact hy
    rw [h0, zero_smul]; exact Q_zero R I n
  · exact Q_smul R I n _ (Q_E R I n hν)

end GlobalTheory.DivPowTrunc

namespace GlobalTheory.DivPowTrunc

variable (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Type) [Fintype I] (n : ℕ)

attribute [local instance] charZero_K

abbrev f : B R I n →+* C R I n := (B R I n).val

def J : Ideal (C R I n) := (RingHom.ker (π R I n)).map (f R I n)

theorem ker_m {y : B R I n} (hy : y ∈ RingHom.ker (π R I n)) : (y : C R I n) ∈ m R I n := by
  apply mem_m
  rw [← π_apply, RingHom.mem_ker.1 hy, map_zero]

theorem dpowJ {y : B R I n} (hy : y ∈ RingHom.ker (π R I n)) (k : ℕ) :
    (DividedPowers.RatAlgebra.dividedPowers (J R I n)).dpow k (f R I n y) = (δ R I n).dpow k (y : C R I n) := by
  have h1 : f R I n y ∈ J R I n := Ideal.mem_map_of_mem _ hy
  simp only [δ, DividedPowers.RatAlgebra.dpow_apply, if_pos h1, if_pos (ker_m R I n hy)]
  rfl

theorem hmem (k : ℕ) {y : B R I n} (hy : y ∈ RingHom.ker (π R I n)) :
    ∃ (z : B R I n) (_ : k ≠ 0 → z ∈ RingHom.ker (π R I n)),
      f R I n z = (DividedPowers.RatAlgebra.dividedPowers (J R I n)).dpow k (f R I n y) := by
  refine ⟨⟨(δ R I n).dpow k (y : C R I n), (integral R I n y hy).2 k⟩, fun hk => ?_, ?_⟩
  · rw [RingHom.mem_ker]
    apply IsFractionRing.injective R (K R)
    rw [π_apply, map_zero]
    exact εC_dpow R I n (ker_m R I n hy) hk
  · rw [dpowJ R I n hy]; rfl

def κ : DividedPowers (RingHom.ker (π R I n)) :=
  DividedPowers.ofInjective (RingHom.ker (π R I n)) (J R I n) (f R I n) Subtype.val_injective
    (DividedPowers.RatAlgebra.dividedPowers (J R I n)) rfl fun k _ hy => hmem R I n k hy

theorem κ_apply {y : B R I n} (hy : y ∈ RingHom.ker (π R I n)) (k : ℕ) :
    (((κ R I n).dpow k y : B R I n) : C R I n) = (δ R I n).dpow k (y : C R I n) := by
  simp only [κ, DividedPowers.ofInjective, dif_pos hy]
  exact (Exists.choose_spec (hmem R I n k hy)).2.trans (dpowJ R I n hy k)

theorem nil : IsNilDP (κ R I n) := by
  refine ⟨n + 2, fun l hl hs => ?_⟩
  have key : ∀ l : List (ℕ × B R I n), (∀ p ∈ l, p.2 ∈ RingHom.ker (π R I n)) →
      (((l.map fun p => (κ R I n).dpow p.1 p.2).prod : B R I n) : C R I n) ∈ m R I n ^ (l.map Prod.fst).sum := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons p l ih =>
      intro h
      have hp : p.2 ∈ RingHom.ker (π R I n) := h p (by simp)
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [Subalgebra.coe_mul, pow_add, κ_apply R I n hp]
      exact Ideal.mul_mem_mul (dpow_mem_pow R I n _ (ker_m R I n hp)) (ih fun q hq => h q (by simp [hq]))
  have h2 := Ideal.pow_le_pow_right hs (key l hl)
  rw [m_pow, Ideal.mem_bot] at h2
  exact Subtype.val_injective h2

def jetRing : JetRing R I n where
  B := B R I n
  b := b R I n
  one := Subtype.ext (by rw [b_apply]; exact E_zero R I n)
  mul ν ν' := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, b_apply, b_apply, E_mul]
    split_ifs with h
    · simp [b_apply]
    · rw [E_big R I n _ (by simp only [Pi.add_apply] at h ⊢; omega)]
      simp
  π := π R I n
  π_eq _ := rfl
  κ := κ R I n
  nil := nil R I n

end GlobalTheory.DivPowTrunc

theorem GlobalTheory.DivPowTrunc.jetRingEx : GlobalTheory.LatJet.JetRingEx :=
  fun R _ _ _ I _ n => ⟨GlobalTheory.DivPowTrunc.jetRing R I n⟩
