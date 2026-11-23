import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsQuasiFinitePolynomialMapStatement

open IsLocalRing

namespace GlobalTheory.QFNN

theorem integralClosure_of_fractions (P A : Type) [CommRing P] [IsDomain P] [IsNoetherianRing P]
    [IsIntegrallyClosed P] [CharZero P] [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsIntegrallyClosed A] [Algebra P A] [Algebra.EssFiniteType P A]
    (hinj : Function.Injective (algebraMap P A))
    (hloc : ∀ a : A, ∃ b t : A, IsIntegral P b ∧ IsIntegral P t ∧ IsUnit t ∧ a * t = b) :
    Module.Finite P (integralClosure P A) ∧ IsIntegrallyClosed (integralClosure P A) ∧
      Function.Injective (algebraMap P (integralClosure P A)) ∧
      IsLocalization.AtPrime A
        ((maximalIdeal A).comap (algebraMap (integralClosure P A) A)) := by
  let K := FractionRing A
  let F := FractionRing P
  let B := integralClosure P A
  have hιinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hPK : Function.Injective (algebraMap P K) := by
    rw [IsScalarTower.algebraMap_eq P A K]
    exact hιinj.comp hinj
  haveI : FaithfulSMul P K := (faithfulSMul_iff_algebraMap_injective P K).mpr hPK
  letI : Algebra F K := FractionRing.liftAlgebra P K
  haveI : IsScalarTower P F K := FractionRing.isScalarTower_liftAlgebra P K

  have halgA : ∀ a : A, IsAlgebraic P (algebraMap A K a) := by
    intro a
    obtain ⟨b, t, hb, ht, hu, hab⟩ := hloc a
    have ht0 : algebraMap A K t ≠ 0 := by
      simpa using (map_ne_zero_iff _ hιinj).mpr hu.ne_zero
    have : algebraMap A K a = algebraMap A K b * (algebraMap A K t)⁻¹ := by
      rw [← hab, map_mul, mul_assoc, mul_inv_cancel₀ ht0, mul_one]
    rw [this]
    exact (hb.algebraMap (B := K)).isAlgebraic.mul (ht.algebraMap (B := K)).isAlgebraic.inv
  haveI hPKalg : Algebra.IsAlgebraic P K := by
    refine ⟨fun x => ?_⟩
    obtain ⟨a, s, _, rfl⟩ := IsFractionRing.div_surjective (A := A) x
    rw [div_eq_mul_inv]
    exact (halgA a).mul (halgA s).inv
  haveI : Algebra.IsAlgebraic F K := (IsFractionRing.comap_isAlgebraic_iff (A := P) (K := F)).mp hPKalg
  haveI : Algebra.EssFiniteType A K := .of_isLocalization K (nonZeroDivisors A)
  haveI : Algebra.EssFiniteType P K := .comp P A K
  haveI : Algebra.EssFiniteType F K := .of_comp P F K
  haveI : FiniteDimensional F K := Algebra.finite_of_essFiniteType_of_isAlgebraic
  haveI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective P F)
  haveI hic : IsIntegralClosure B P K :=
    { algebraMap_injective := hιinj.comp Subtype.val_injective
      isIntegral_iff := by
        intro x
        constructor
        · intro hx
          obtain ⟨a, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hx.tower_top (A := A))
          have ha : IsIntegral P a := (isIntegral_algebraMap_iff hιinj).mp hx
          exact ⟨⟨a, ha⟩, rfl⟩
        · rintro ⟨y, rfl⟩
          exact (y.2.algebraMap (B := K)) }
  haveI hfrac : IsFractionRing B K := IsIntegralClosure.isFractionRing_of_finite_extension P F K B
  refine ⟨IsIntegralClosure.finite P F K B, ?_, ?_, ?_⟩
  · refine (isIntegrallyClosed_iff K).mpr ?_
    intro x hx
    have hxP : IsIntegral P x := isIntegral_trans x hx
    exact (IsIntegralClosure.isIntegral_iff (A := B)).mp hxP
  · intro x y h
    exact hinj (congrArg Subtype.val h)
  · have hne : ∀ b : B, b ∈ ((maximalIdeal A).comap (algebraMap B A)).primeCompl →
        IsUnit (algebraMap B A b) := by
      intro b hb
      by_contra hu
      exact hb ((mem_maximalIdeal _).mpr hu)
    refine ⟨fun y => hne y.1 y.2, fun a => ?_, fun {x y} h => ⟨1, ?_⟩⟩
    · obtain ⟨b, t, hb, ht, hu, hab⟩ := hloc a
      refine ⟨(⟨b, hb⟩, ⟨⟨t, ht⟩, ?_⟩), hab⟩
      intro hmem
      exact (mem_maximalIdeal _).mp hmem hu
    · have : x = y := Subtype.val_injective h
      rw [this]

end GlobalTheory.QFNN

theorem GlobalTheory.normal_local_is_localisation_of_finite_over_polynomial :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [CharZero A]
      [Algebra.EssFiniteType ℤ A], ∃ (r : ℕ) (B : Type) (_ : CommRing B) (_ : IsDomain B)
      (_ : IsIntegrallyClosed B) (_ : Algebra (MvPolynomial (Fin r) ℤ) B)
      (_ : Module.Finite (MvPolynomial (Fin r) ℤ) B) (_ : Algebra B A) (𝔫 : Ideal B) (_ : 𝔫.IsPrime),
      Function.Injective (algebraMap (MvPolynomial (Fin r) ℤ) B) ∧ IsLocalization.AtPrime A 𝔫 := by
  intro A _ _ _ _ _ hess
  obtain ⟨S₀, M, hft, hlocM⟩ := (Algebra.essFiniteType_iff_exists_subalgebra ℤ A).mp hess
  let 𝔮 : Ideal S₀ := (maximalIdeal A).comap (algebraMap S₀ A)
  haveI h𝔮 : 𝔮.IsPrime := Ideal.comap_isPrime _ _
  have hunit : ∀ s : S₀, s ∉ 𝔮 → IsUnit (algebraMap S₀ A s) := by
    intro s hs
    by_contra hu
    exact hs ((mem_maximalIdeal _).mpr hu)
  have hM : M ≤ 𝔮.primeCompl := by
    intro m hm hmem
    exact (mem_maximalIdeal _).mp hmem (IsLocalization.map_units A ⟨m, hm⟩)
  haveI hat : IsLocalization 𝔮.primeCompl A :=
    IsLocalization.of_le M _ hM (fun s hs => hunit s hs)
  haveI : CharZero S₀ := (algebraMap S₀ A).charZero
  obtain ⟨r, y, hy, hqf⟩ := GlobalTheory.T.exists_quasi_finite_polynomial_map S₀ 𝔮
  let P := MvPolynomial (Fin r) ℤ
  letI algPS : Algebra P S₀ := (MvPolynomial.aeval y : P →ₐ[ℤ] S₀).toRingHom.toAlgebra
  letI algPA : Algebra P A := ((algebraMap S₀ A).comp (algebraMap P S₀)).toAlgebra
  haveI : IsScalarTower P S₀ A := .of_algebraMap_eq' rfl
  haveI : IsScalarTower ℤ P S₀ := .of_algebraMap_eq' (RingHom.ext_int _ _)
  haveI : IsScalarTower ℤ P A := .of_algebraMap_eq' (RingHom.ext_int _ _)
  haveI : Algebra.FiniteType P S₀ := .of_restrictScalars_finiteType ℤ P S₀
  haveI : Algebra.EssFiniteType P A := .of_comp ℤ P A
  have hinj : Function.Injective (algebraMap P A) :=
    (Subtype.val_injective : Function.Injective (algebraMap S₀ A)).comp
      ((algebraicIndependent_iff_injective_aeval).mp hy)
  have hzmp : Algebra.ZariskisMainProperty P 𝔮 := Algebra.ZariskisMainProperty.of_finiteType 𝔮
  obtain ⟨ρ, hρq, hρ, H⟩ := Algebra.zariskisMainProperty_iff.mp hzmp
  have hloc : ∀ a : A, ∃ b t : A, IsIntegral P b ∧ IsIntegral P t ∧ IsUnit t ∧ a * t = b := by
    intro a
    obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.surj 𝔮.primeCompl a
    obtain ⟨m₁, h₁⟩ := H x
    obtain ⟨m₂, h₂⟩ := H s
    have hb : IsIntegral P (ρ ^ (m₁ + m₂) * x) := by
      have : ρ ^ (m₁ + m₂) * x = ρ ^ m₂ * (ρ ^ m₁ * x) := by ring
      rw [this]
      exact (hρ.pow _).mul h₁
    have ht : IsIntegral P (ρ ^ (m₁ + m₂) * (s : S₀)) := by
      have : ρ ^ (m₁ + m₂) * (s : S₀) = ρ ^ m₁ * (ρ ^ m₂ * (s : S₀)) := by ring
      rw [this]
      exact (hρ.pow _).mul h₂
    refine ⟨_, _, hb.algebraMap (B := A), ht.algebraMap (B := A), hunit _ ?_, ?_⟩
    · exact h𝔮.mul_notMem (fun h => hρq (h𝔮.mem_of_pow_mem _ h)) s.2
    · simp only [map_mul, map_pow]
      rw [← hxs]
      ring
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.QFNN.integralClosure_of_fractions P A hinj hloc
  exact ⟨r, integralClosure P A, inferInstance, inferInstance, h2, inferInstance, h1, inferInstance,
    _, Ideal.comap_isPrime _ _, h3, h4⟩
