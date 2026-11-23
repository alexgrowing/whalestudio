import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.FiniteIntegralClosureLocal
set_option maxSynthPendingDepth 1

open scoped nonZeroDivisors

namespace GroundTheory.Heights₂.Heights.Model

theorem isJacobsonRing_int : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases h0 : P = ⊥
  · subst h0
    refine le_antisymm (fun x hx => ?_) Ideal.le_jacobson
    rw [Ideal.mem_jacobson_iff] at hx
    obtain ⟨z₁, hz₁⟩ := hx 1
    obtain ⟨z₂, hz₂⟩ := hx 2
    rw [Ideal.mem_bot] at hz₁ hz₂ ⊢
    have e1 : (x + 1) * z₁ = 1 := by linear_combination hz₁
    have e2 : (2 * x + 1) * z₂ = 1 := by linear_combination hz₂
    have h1 : IsUnit (x + 1) := ⟨⟨x + 1, z₁, e1, (mul_comm _ _).trans e1⟩, rfl⟩
    have h2 : IsUnit (2 * x + 1) := ⟨⟨2 * x + 1, z₂, e2, (mul_comm _ _).trans e2⟩, rfl⟩
    rw [Int.isUnit_iff] at h1 h2
    omega
  · have : P.IsMaximal := IsPrime.to_maximal_ideal h0
    exact Ideal.jacobson_eq_self_of_isMaximal

theorem exists_prime_mem_of_isMaximal (A : Type*) [CommRing A] [Algebra.FiniteType ℤ A]
    (𝔪 : Ideal A) [𝔪.IsMaximal] : ∃ p : ℕ, p.Prime ∧ (p : A) ∈ 𝔪 := by
  let _ := Ideal.Quotient.field 𝔪
  have := isJacobsonRing_int
  have : Algebra.FiniteType ℤ (A ⧸ 𝔪) := inferInstance
  have : Module.Finite ℤ (A ⧸ 𝔪) := finite_of_finite_type_of_isJacobsonRing ℤ (A ⧸ 𝔪)
  obtain ⟨p, hp⟩ := CharP.exists (A ⧸ 𝔪)
  rcases CharP.char_is_prime_or_zero (A ⧸ 𝔪) p with hp' | rfl
  · refine ⟨p, hp', ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ p
  · exfalso
    have : CharZero (A ⧸ 𝔪) := CharP.charP_to_charZero (A ⧸ 𝔪)
    have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := ℤ) (⊥ : Ideal (A ⧸ 𝔪))
    have hbot : (⊥ : Ideal (A ⧸ 𝔪)).comap (algebraMap ℤ (A ⧸ 𝔪)) = ⊥ := by
      rw [← RingHom.ker_eq_comap_bot, RingHom.ker_eq_bot_iff_eq_zero]
      intro n hn
      exact_mod_cast (show ((n : ℤ) : A ⧸ 𝔪) = 0 by simpa using hn)
    rw [hbot] at hmax
    exact Int.not_isField (Ring.isField_iff_maximal_bot.mpr hmax)

theorem exists_pow_smul_mem_of_isMaximal
    (A : Type*) [CommRing A] [IsDomain A] [CharZero A] [Algebra.FiniteType ℤ A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (𝔪 : Ideal A) [𝔪.IsMaximal] :
    ∃ r ∉ 𝔪, ∃ N : Submodule A (integralClosure A K), N.FG ∧
      ∀ x : integralClosure A K, ∃ n : ℕ, r ^ n • x ∈ N := by
  classical
  obtain ⟨p, hp, hp𝔪⟩ := exists_prime_mem_of_isMaximal A 𝔪
  have : Fact p.Prime := ⟨hp⟩
  set I : Ideal A := Ideal.span {(p : A)}
  have hI𝔪 : I ≤ 𝔪 := (Ideal.span_singleton_le_iff_mem _).mpr hp𝔪
  have : Nontrivial (A ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (Ideal.IsMaximal.ne_top ‹_›) hI𝔪)
  have : CharP (A ⧸ I) p := (CharP.charP_iff_prime_eq_zero hp).mpr (by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl)
  let _ : Algebra (ZMod p) (A ⧸ I) := ZMod.algebra (A ⧸ I) p
  have : Algebra.FiniteType (ZMod p) (A ⧸ I) :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ZMod p) (A ⧸ I)
  obtain ⟨d, g, hginj, hgfin⟩ := exists_finite_inj_algHom_of_fg (ZMod p) (A ⧸ I)
  have hy : ∀ i, ∃ y : A, Ideal.Quotient.mk I y = g (MvPolynomial.X i) :=
    fun i => Ideal.Quotient.mk_surjective _
  choose y hy using hy
  set C := MvPolynomial (Fin d) ℤ
  let φ : C →ₐ[ℤ] A := MvPolynomial.aeval y
  let red : C →+* MvPolynomial (Fin d) (ZMod p) := MvPolynomial.map (Int.castRingHom (ZMod p))
  have hkey : ∀ F : C, Ideal.Quotient.mk I (φ F) = g (red F) := by
    intro F
    have : (Ideal.Quotient.mk I).comp φ.toRingHom = g.toRingHom.comp red :=
      MvPolynomial.ringHom_ext (fun n => by simp [φ, red]) (fun i => by
        change Ideal.Quotient.mk I (MvPolynomial.aeval y (MvPolynomial.X i)) =
          g (MvPolynomial.map _ (MvPolynomial.X i))
        rw [MvPolynomial.aeval_X, MvPolynomial.map_X, hy])
    exact congrArg (fun f => f F) this
  have hp0 : (p : A) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hstep : ∀ F : C, φ F = 0 → ∃ G, F = MvPolynomial.C (p : ℤ) * G ∧ φ G = 0 := by
    intro F hF
    have h1 : red F = 0 := hginj (by rw [← hkey, hF, map_zero, map_zero])
    have h2 : F ∈ RingHom.ker red := h1
    rw [MvPolynomial.ker_map, ZMod.ker_intCastRingHom, Ideal.map_span, Set.image_singleton] at h2
    obtain ⟨G, hG⟩ := Ideal.mem_span_singleton'.mp h2
    refine ⟨G, by rw [← hG, mul_comm], ?_⟩
    rw [← hG, map_mul, MvPolynomial.aeval_C, algebraMap_int_eq, eq_intCast, Int.cast_natCast] at hF
    exact (mul_eq_zero.mp hF).resolve_right hp0
  have hpow : ∀ k : ℕ, ∀ F : C, φ F = 0 → ∃ G, F = MvPolynomial.C ((p : ℤ) ^ k) * G := by
    intro k
    induction k with
    | zero => intro F _; exact ⟨F, by simp⟩
    | succ k ih =>
      intro F hF
      obtain ⟨G, rfl, hG⟩ := hstep F hF
      obtain ⟨H, rfl⟩ := ih G hG
      exact ⟨H, by rw [pow_succ, map_mul, mul_assoc, mul_left_comm]⟩
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro F hF
    ext m
    rw [MvPolynomial.coeff_zero]
    by_contra hc
    obtain ⟨G, hG⟩ := hpow (MvPolynomial.coeff m F).natAbs F hF
    have hdvd : (p : ℤ) ^ (MvPolynomial.coeff m F).natAbs ∣ MvPolynomial.coeff m F :=
      ⟨MvPolynomial.coeff m G, by conv_lhs => rw [hG]
                                  rw [MvPolynomial.coeff_C_mul]⟩
    have h1 := Int.natAbs_dvd_natAbs.mpr hdvd
    rw [Int.natAbs_pow, Int.natAbs_natCast] at h1
    have h2 := Nat.le_of_dvd (Int.natAbs_pos.mpr hc) h1
    exact absurd h2 (not_le.mpr (Nat.lt_pow_self hp.one_lt))
  let _ : Algebra C A := φ.toRingHom.toAlgebra
  have : IsScalarTower ℤ C A := IsScalarTower.of_algebraMap_eq fun n => by simp
  have : Algebra.FiniteType C A := Algebra.FiniteType.of_restrictScalars_finiteType ℤ C A
  have : Algebra.WeaklyQuasiFiniteAt C 𝔪 := by
    rw [Algebra.weaklyQuasiFiniteAt_iff]
    let _ : Algebra (MvPolynomial (Fin d) (ZMod p)) (A ⧸ I) := g.toRingHom.toAlgebra
    have : Module.Finite (MvPolynomial (Fin d) (ZMod p)) (A ⧸ I) := hgfin
    let _ : Algebra C (MvPolynomial (Fin d) (ZMod p)) := red.toAlgebra
    have : IsScalarTower C (MvPolynomial (Fin d) (ZMod p)) (A ⧸ I) :=
      IsScalarTower.of_algebraMap_eq fun F => hkey F
    have : Module.Finite C (MvPolynomial (Fin d) (ZMod p)) :=
      Module.Finite.of_surjective (Algebra.linearMap C _)
        (MvPolynomial.map_surjective _ (ZMod.intCast_surjective))
    have : Module.Finite C (A ⧸ I) := Module.Finite.trans (MvPolynomial (Fin d) (ZMod p)) (A ⧸ I)
    set L := Localization.AtPrime 𝔪
    set J := (𝔪.under C).map (algebraMap C L)
    have hpJ : ((p : ℕ) : L) ∈ J := by
      have hmem : ((p : ℕ) : C) ∈ 𝔪.under C := by
        change algebraMap C A (p : C) ∈ 𝔪
        rw [map_natCast]
        exact hp𝔪
      have := Ideal.mem_map_of_mem (algebraMap C L) hmem
      rwa [map_natCast] at this
    let f₀ : A →ₐ[C] L ⧸ J := (Ideal.Quotient.mkₐ C J).comp (IsScalarTower.toAlgHom C A L)
    have hf₀ : ∀ a ∈ I, f₀ a = 0 := by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      simp only [f₀, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, Ideal.Quotient.mkₐ_eq_mk,
        map_mul, map_natCast]
      have hp' : ((p : ℕ) : L ⧸ J) = 0 := by
        rw [← map_natCast (Ideal.Quotient.mk J), Ideal.Quotient.eq_zero_iff_mem]
        exact hpJ
      rw [hp', mul_zero]
    let f : (A ⧸ I) →ₐ[C] L ⧸ J := Ideal.Quotient.liftₐ I f₀ hf₀
    refine Algebra.QuasiFinite.of_forall_exists_mul_mem_range f fun x => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔪.primeCompl x
    refine ⟨Ideal.Quotient.mk I s, ?_, ⟨Ideal.Quotient.mk I a, ?_⟩⟩
    · exact (IsLocalization.map_units L s).map (Ideal.Quotient.mk J)
    · change f₀ a = _ * f₀ s
      simp only [f₀, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, Ideal.Quotient.mkₐ_eq_mk]
      rw [← map_mul, IsLocalization.mk'_spec]
  exact exists_pow_smul_mem_of_weaklyQuasiFiniteAt A K d hφinj 𝔪

theorem finite_integralClosure_fractionRing_of_charZero
    (A : Type*) [CommRing A] [IsDomain A] [CharZero A] [Algebra.FiniteType ℤ A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K] :
    Module.Finite A (integralClosure A K) :=
  module_finite_of_forall_isMaximal fun 𝔪 _ => exists_pow_smul_mem_of_isMaximal A K 𝔪

theorem finite_integralClosure_of_charZero
    (A : Type*) [CommRing A] [IsDomain A] [CharZero A] [Algebra.FiniteType ℤ A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A K L] :
    Module.Finite A (integralClosure A L) := by
  have : Module.Finite A (integralClosure A K) :=
    finite_integralClosure_fractionRing_of_charZero A K
  set A' := integralClosure A K
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  have : IsNoetherianRing A' := IsNoetherianRing.of_finite A A'
  have : IsIntegrallyClosed A' := integralClosure.isIntegrallyClosedOfFiniteExtension K (L := K)
  have : IsFractionRing A' K := integralClosure.isFractionRing_of_finite_extension K K
  have : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective A K)
  have : Algebra.IsSeparable K L := Algebra.IsSeparable.of_integral K L
  have : IsScalarTower A' K L := inferInstance
  have : IsScalarTower A A' L := inferInstance
  have : Module.Finite A' (integralClosure A' L) :=
    IsIntegralClosure.finite A' K L (integralClosure A' L)
  have : Module.Finite A (integralClosure A' L) := Module.Finite.trans A' _
  have hle : (integralClosure A L).toSubmodule ≤
      (integralClosure A' L).toSubmodule.restrictScalars A := fun y hy => hy.tower_top
  have : IsNoetherian A ((integralClosure A' L).toSubmodule.restrictScalars A) :=
    isNoetherian_of_isNoetherianRing_of_finite A (integralClosure A' L)
  have : IsNoetherian A (integralClosure A L).toSubmodule := isNoetherian_of_le hle
  exact Module.IsNoetherian.finite A (integralClosure A L).toSubmodule

end GroundTheory.Heights₂.Heights.Model
