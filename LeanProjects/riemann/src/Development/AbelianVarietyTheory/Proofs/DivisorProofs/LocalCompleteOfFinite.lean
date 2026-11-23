import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts

open IsLocalRing

namespace GlobalTheory.FiniteLocalCompleteness

theorem precomplete_of_finite {R : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R] (M : Type) [AddCommGroup M]
    [Module R M] [Module.Finite R M] : IsPrecomplete I M := by
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M y
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul r x =>
    obtain ⟨a, rfl⟩ := AdicCompletion.of_surjective I R r
    refine ⟨a • x, ?_⟩
    rw [AdicCompletion.ofTensorProduct_tmul, map_smul]
    have : AdicCompletion.of I R a = algebraMap R (AdicCompletion I R) a := rfl
    rw [this, algebraMap_smul]
  | add s t hs ht =>
    obtain ⟨a, ha⟩ := hs
    obtain ⟨b, hb⟩ := ht
    exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩

theorem precomplete_of_pow_le {S : Type} [CommRing S] (I J : Ideal S) [hI : IsPrecomplete I S] (hIJ : I ≤ J) (k : ℕ)
    (hk : J ^ (k + 1) ≤ I) : IsPrecomplete J S := by
  refine ⟨fun f hf => ?_⟩
  have h1 : ∀ n, (J ^ ((k + 1) * n) • ⊤ : Submodule S S) ≤ I ^ n • ⊤ := fun n => by
    refine Submodule.smul_mono_left ?_
    rw [pow_mul]
    exact Ideal.pow_right_mono hk n
  obtain ⟨L, hL⟩ := hI.prec (f := fun n => f ((k + 1) * n))
    (fun {m n} h => (hf (Nat.mul_le_mul_left _ h)).mono (h1 m))
  refine ⟨L, fun n => ?_⟩
  refine (hf (show n ≤ (k + 1) * n by nlinarith)).trans ((hL n).mono ?_)
  exact Submodule.smul_mono_left (Ideal.pow_right_mono hIJ n)

theorem isLocalRing_of_complete {S : Type} [CommRing S] [IsDomain S] (I : Ideal S) [IsAdicComplete I S]
    [IsArtinianRing (S ⧸ I)] : IsLocalRing S := by
  have hjac := IsAdicComplete.le_jacobson_bot I
  have hu : ∀ z ∈ I, IsUnit (1 - z) := fun z hz => by
    have := Ideal.mem_jacobson_bot.1 (hjac (I.neg_mem hz)) 1
    simpa [sub_eq_add_neg, add_comm] using this
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  obtain ⟨n, y', hy⟩ := IsArtinian.exists_pow_succ_smul_dvd (Ideal.Quotient.mk I x) (1 : S ⧸ I)
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y'
  simp only [smul_eq_mul, mul_one] at hy
  set X := Ideal.Quotient.mk I x with hX
  set Y := Ideal.Quotient.mk I y with hY
  have hk : ∀ k : ℕ, X ^ n * (X * Y) ^ k = X ^ n := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      calc X ^ n * (X * Y) ^ (k + 1) = (X ^ (n + 1) * Y) * (X * Y) ^ k := by ring
        _ = X ^ n := by rw [Nat.succ_eq_add_one] at hy; rw [hy, ih]
  have he : ((X * Y) ^ n) ^ 2 = (X * Y) ^ n := by
    calc ((X * Y) ^ n) ^ 2 = (X ^ n * (X * Y) ^ n) * Y ^ n := by ring
      _ = (X * Y) ^ n := by rw [hk]; ring
  have hE : Ideal.Quotient.mk I ((x * y) ^ n) = (X * Y) ^ n := by simp [hX, hY]
  obtain ⟨a, ha, hae⟩ := HenselianRing.is_henselian (I := I) (Polynomial.X ^ 2 - Polynomial.X : Polynomial S)
    (by monicity!) ((x * y) ^ n)
    (by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, map_sub]
      rw [map_pow, hE, he, sub_self])
    (by
      have : Ideal.Quotient.mk I (Polynomial.eval ((x * y) ^ n)
          (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.X : Polynomial S))) = 2 * (X * Y) ^ n - 1 := by
        rw [← hE]
        simp [one_add_one_eq_two, map_ofNat]
      rw [this]
      exact IsUnit.of_mul_eq_one (2 * (X * Y) ^ n - 1) (by linear_combination 4 * he))
  have ha' : a * (a - 1) = 0 := by
    have : a ^ 2 - a = 0 := by simpa using ha
    linear_combination this
  rcases mul_eq_zero.1 ha' with h0 | h0
  · right
    subst h0
    have h2 : (X * Y) ^ n = 0 := by
      rw [← hE, Ideal.Quotient.eq_zero_iff_mem]
      simpa using hae
    have h3 : x ^ n ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow, ← hX, ← hk n, h2, mul_zero]
    exact isUnit_of_dvd_unit (one_sub_dvd_one_sub_pow x n) (hu _ h3)
  · obtain rfl : a = 1 := sub_eq_zero.1 h0
    have h2 := hu _ hae
    rw [sub_sub_cancel] at h2
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h3 := hk 1
      left
      have h4 : 1 - x * y ∈ I := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        simp only [pow_zero, pow_one, one_mul] at h3
        rw [map_sub, map_one, map_mul, ← hX, ← hY, h3, sub_self]
      have h5 := hu _ h4
      rw [sub_sub_cancel] at h5
      exact isUnit_of_mul_isUnit_left h5
    · left
      exact isUnit_of_mul_isUnit_left ((isUnit_pow_iff hn.ne').1 h2)

theorem local_complete_of_finite (R S : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S] :
    ∃ _ : IsLocalRing S, IsAdicComplete (maximalIdeal S) S := by
  haveI : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  haveI : IsPrecomplete (maximalIdeal R) S := precomplete_of_finite _ S
  haveI : IsAdicComplete (maximalIdeal R) S := ⟨⟩
  set I := (maximalIdeal R).map (algebraMap R S) with hI
  haveI : IsAdicComplete I S := (IsAdicComplete.map_algebraMap_iff _ _).2 inferInstance
  haveI : IsArtinianRing (S ⧸ I) := by
    letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
    haveI : Module.Finite (R ⧸ maximalIdeal R) (S ⧸ I) := Module.Finite.of_restrictScalars_finite R _ _
    exact IsArtinianRing.of_finite (R ⧸ maximalIdeal R) _
  haveI hl : IsLocalRing S := isLocalRing_of_complete I
  refine ⟨hl, ?_⟩
  have hne : I ≠ ⊤ := by
    intro h
    have := IsAdicComplete.le_jacobson_bot I
    rw [h, IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top] at this
    exact (maximalIdeal.isMaximal S).ne_top (top_le_iff.1 this)
  have hrad : maximalIdeal S ≤ I.radical := by
    intro x hx
    obtain ⟨n, y', hy⟩ := IsArtinian.exists_pow_succ_smul_dvd (Ideal.Quotient.mk I x) (1 : S ⧸ I)
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y'
    simp only [smul_eq_mul, mul_one, Nat.succ_eq_add_one] at hy
    have hu : IsUnit (1 - x * y) :=
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (Ideal.mul_mem_right y (maximalIdeal S) hx)
    refine ⟨n, (Ideal.mul_unit_mem_iff_mem I hu).1 ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [map_mul, map_pow, map_sub, map_one]
    linear_combination -hy
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  haveI : IsPrecomplete (maximalIdeal S) S :=
    precomplete_of_pow_le I _ (le_maximalIdeal hne) k ((Ideal.pow_le_pow_right (Nat.le_succ k)).trans hk)
  exact ⟨⟩

theorem exists_normal (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : Type) [CommRing D] [IsDomain D]
    [Algebra R D] [Module.Finite R D] [FaithfulSMul R D] (hR : GlobalTheory.TorRef.IsCN R) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (σ : D →+* R'),
      GlobalTheory.TorRef.IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ σ.comp (algebraMap R D) = ρ := by
  obtain ⟨h1, h2, h3, h4⟩ := hR
  letI : Algebra (FractionRing R) (FractionRing D) := FractionRing.liftAlgebra R (FractionRing D)
  haveI : IsScalarTower R (FractionRing R) (FractionRing D) := FractionRing.isScalarTower_liftAlgebra R _
  haveI : FiniteDimensional (FractionRing R) (FractionRing D) :=
    Module.Finite.of_isLocalization R D (nonZeroDivisors R) (Rₚ := FractionRing R) (Sₚ := FractionRing D)
  haveI : CharZero (FractionRing R) := IsFractionRing.charZero_of_isFractionRing R
  haveI : Algebra.IsIntegral (FractionRing R) (FractionRing D) := Algebra.IsIntegral.of_finite _ _
  haveI : Algebra.IsSeparable (FractionRing R) (FractionRing D) := Algebra.IsSeparable.of_integral _ _
  let S := integralClosure R (FractionRing D)
  haveI : Module.Finite R S := IsIntegralClosure.finite R (FractionRing R) (FractionRing D) S
  haveI : IsIntegrallyClosed S := integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing R)
  have hL : Function.Injective (algebraMap R (FractionRing D)) := FaithfulSMul.algebraMap_injective R _
  have hS : Function.Injective (algebraMap R S) := fun a b h => hL (congrArg Subtype.val h)
  haveI : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective _ _).2 hS
  obtain ⟨hl, hc⟩ := local_complete_of_finite R S
  let ψ : D →ₐ[R] FractionRing D := IsScalarTower.toAlgHom R D _
  let σ : D →ₐ[R] S := ψ.codRestrict S fun c => (Algebra.IsIntegral.isIntegral c).map ψ
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite _ _
  refine ⟨S, inferInstance, inferInstance, hl, algebraMap R S, σ.toRingHom,
    ⟨IsNoetherianRing.of_finite R S, inferInstance, hc, charZero_of_injective_algebraMap hS⟩, hS,
    RingHom.finite_algebraMap.2 inferInstance, Algebra.IsIntegral.isLocalHom R S, σ.comp_algebraMap⟩

theorem main (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (C : Type) [CommRing C] (φ : R →+* C)
    (hR : GlobalTheory.TorRef.IsCN R) (hφ : Function.Injective φ) (hfin : φ.Finite) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (σ : C →+* R'),
      GlobalTheory.TorRef.IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ σ.comp φ = ρ := by
  letI : Algebra R C := φ.toAlgebra
  haveI : Module.Finite R C := hfin
  obtain ⟨P, -, hP, hPc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (R := R) (S := C) (⊥ : Ideal R) ⊥
    (by rw [← RingHom.ker_eq_comap_bot]; exact ((RingHom.injective_iff_ker_eq_bot _).1 hφ).le)
  have hD : Function.Injective (algebraMap R (C ⧸ P)) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have : a ∈ P.comap (algebraMap R C) := by
      rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
      exact ha
    rwa [hPc] at this
  haveI : FaithfulSMul R (C ⧸ P) := (faithfulSMul_iff_algebraMap_injective _ _).2 hD
  obtain ⟨R', i1, i2, i3, ρ, σ, h1, h2, h3, h4, h5⟩ := exists_normal R (C ⧸ P) hR
  exact ⟨R', i1, i2, i3, ρ, σ.comp (Ideal.Quotient.mk P), h1, h2, h3, h4, h5⟩

end GlobalTheory.FiniteLocalCompleteness
