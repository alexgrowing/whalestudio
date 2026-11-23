import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscrMulMemOfIsIntegralStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingEquivAdicCompletionLocalizationProdStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConductorProdFstStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalLocalIsLocalisationOfFiniteOverPolynomialAStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRegularLocalRingAdicCompletionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomainStatement

open IsLocalRing TensorProduct

namespace GlobalTheory

theorem exists_finite_over_localization_atPrime_below (P B A : Type) [CommRing P] [CommRing B]
    [IsDomain B] [Algebra P B] [Module.Finite P B] [CommRing A] [IsLocalRing A] [Algebra B A]
    (𝔫 : Ideal B) [𝔫.IsPrime] [IsLocalization.AtPrime A 𝔫]
    (hinj : Function.Injective (algebraMap P B)) :
    ∃ (p : Ideal P) (_ : p.IsPrime) (C : Type) (_ : CommRing C) (_ : IsDomain C)
      (_ : Algebra (Localization.AtPrime p) C) (_ : Module.Finite (Localization.AtPrime p) C)
      (_ : Algebra C A) (𝔪 : Ideal C) (_ : 𝔪.IsPrime),
      Function.Injective (algebraMap (Localization.AtPrime p) C) ∧ IsLocalization.AtPrime A 𝔪 ∧
        𝔪.comap (algebraMap (Localization.AtPrime p) C) = maximalIdeal (Localization.AtPrime p) := by
  classical
  let p : Ideal P := 𝔫.comap (algebraMap P B)
  have hp : p.IsPrime := Ideal.comap_isPrime _ _
  let M : Submonoid B := Algebra.algebraMapSubmonoid B p.primeCompl
  have hMle : M ≤ 𝔫.primeCompl := by
    rintro _ ⟨s, hs, rfl⟩ h
    exact hs (Ideal.mem_comap.mpr h)
  have hM0 : M ≤ nonZeroDivisors B := by
    rintro _ ⟨s, hs, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => hs ?_
    show algebraMap P B s ∈ 𝔫
    rw [h0]
    exact 𝔫.zero_mem
  have : IsDomain (Localization M) := IsLocalization.isDomain_localization hM0
  let algCA : Algebra (Localization M) A :=
    IsLocalization.localizationAlgebraOfSubmonoidLe (Localization M) A M 𝔫.primeCompl hMle
  have : IsScalarTower B (Localization M) A :=
    IsLocalization.localization_isScalarTower_of_submonoid_le (Localization M) A M 𝔫.primeCompl hMle
  let 𝔪 : Ideal (Localization M) := (maximalIdeal A).comap (algebraMap (Localization M) A)
  have h𝔪 : 𝔪.IsPrime := Ideal.comap_isPrime _ _
  have hNA : IsLocalization (𝔫.primeCompl.map (algebraMap B (Localization M))) A :=
    IsLocalization.isLocalization_of_submonoid_le (Localization M) A M 𝔫.primeCompl hMle
  have hunitB : ∀ b : B, IsUnit (algebraMap B A b) ↔ b ∈ 𝔫.primeCompl := fun b =>
    IsLocalization.AtPrime.isUnit_to_map_iff A 𝔫 b
  have hA : IsLocalization.AtPrime A 𝔪 := by
    refine IsLocalization.isLocalization_of_is_exists_mul_mem (S := A)
      (M := 𝔫.primeCompl.map (algebraMap B (Localization M))) (N := 𝔪.primeCompl) ?_ ?_
    · rintro _ ⟨b, hb, rfl⟩ h
      have hu : IsUnit (algebraMap B A b) := (hunitB b).mpr hb
      rw [IsScalarTower.algebraMap_apply B (Localization M) A] at hu
      exact (IsLocalRing.mem_maximalIdeal _).mp (Ideal.mem_comap.mp h) hu
    · rintro ⟨x, hx⟩
      obtain ⟨b, s, rfl⟩ := IsLocalization.exists_mk'_eq M x
      have key : algebraMap B A b =
          algebraMap B A s * algebraMap (Localization M) A (IsLocalization.mk' (Localization M) b s) := by
        rw [IsScalarTower.algebraMap_apply B (Localization M) A b,
          IsScalarTower.algebraMap_apply B (Localization M) A s, ← map_mul, IsLocalization.mk'_spec']
      refine ⟨algebraMap B (Localization M) s, b, ?_, (IsLocalization.mk'_spec' _ _ _).symm⟩
      have hs : IsUnit (algebraMap B A s) := (hunitB s).mpr (hMle s.2)
      have hx' : IsUnit (algebraMap (Localization M) A (IsLocalization.mk' (Localization M) b s)) := by
        by_contra hn
        exact hx (Ideal.mem_comap.mpr ((IsLocalRing.mem_maximalIdeal _).mpr hn))
      refine (hunitB b).mp ?_
      rw [key]
      exact hs.mul hx'
  have hcomapB : 𝔪.comap (algebraMap B (Localization M)) = 𝔫 := by
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
    exact IsLocalization.AtPrime.under_maximalIdeal A 𝔫
  refine ⟨p, hp, Localization M, inferInstance, inferInstance, inferInstance, inferInstance, algCA,
    𝔪, h𝔪, ?_, hA, ?_⟩
  · exact localizationAlgebra_injective (S := B) (M := p.primeCompl) (Localization.AtPrime p)
      (Localization M) hinj
  · let Q : Ideal (Localization.AtPrime p) :=
      𝔪.comap (algebraMap (Localization.AtPrime p) (Localization M))
    have hQ : Q.comap (algebraMap P (Localization.AtPrime p)) = p := by
      show (𝔪.comap _).comap _ = p
      rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq,
        IsScalarTower.algebraMap_eq P B (Localization M), ← Ideal.comap_comap, hcomapB]
    have h1 : Q = p.map (algebraMap P (Localization.AtPrime p)) := by
      have h2 := IsLocalization.map_under p.primeCompl (Localization.AtPrime p) Q
      rw [Ideal.under_def, hQ] at h2
      exact h2.symm
    show Q = _
    rw [h1]
    exact Localization.AtPrime.map_eq_maximalIdeal

theorem exists_conductor_adicCompletion_of_essFiniteType : ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [CharZero A] [Algebra.EssFiniteType ℤ A], ∃ x : A, x ≠ 0 ∧ ∀ c : FractionRing (AdicCompletion (maximalIdeal A) A), IsIntegral (AdicCompletion (maximalIdeal A) A) c → ∃ s : AdicCompletion (maximalIdeal A) A, algebraMap _ (FractionRing (AdicCompletion (maximalIdeal A) A)) s = algebraMap _ (FractionRing (AdicCompletion (maximalIdeal A) A)) (algebraMap A (AdicCompletion (maximalIdeal A) A) x) * c := by
  intro A _ _ _ _ _ _
  obtain ⟨r, B, _, _, _, _, _, _, 𝔫, _, hinj, hloc⟩ := GlobalTheory.T.injective_and_isLocalization_of_finite_over_mvPolynomial A
  obtain ⟨p, _, C, _, _, _, _, _, 𝔪, _, hinjC, hlocC, hcomap⟩ :=
    exists_finite_over_localization_atPrime_below (MvPolynomial (Fin r) ℤ) B A 𝔫 hinj
  have hTreg : IsRegularLocalRing (Localization.AtPrime p) := inferInstance
  obtain ⟨_, _⟩ := GlobalTheory.T.regular_local_ring_normal_domain (Localization.AtPrime p)
  have := GlobalTheory.T.isRegularLocalRing_adicCompletion' (Localization.AtPrime p)
  obtain ⟨_, _⟩ := GlobalTheory.T.regular_local_ring_normal_domain
    (AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p))
  have : CharZero (Localization.AtPrime p) :=
    charZero_of_injective_algebraMap (R := MvPolynomial (Fin r) ℤ)
      (IsLocalization.injective (M := p.primeCompl) (S := Localization.AtPrime p)
        p.primeCompl_le_nonZeroDivisors)
  have hTU : Function.Injective (algebraMap (Localization.AtPrime p)
      (AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p))) := by
    intro x y h
    exact AdicCompletion.of_injective (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p) h
  obtain ⟨d, hd0, hd⟩ := GlobalTheory.T.exists_ne_zero_mul_integral_eq_tensor (Localization.AtPrime p)
    (AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p)) C hTU hinjC
  obtain ⟨S', _, e, he⟩ := GlobalTheory.T.exists_ringEquiv_adicCompletion_localization_prod (Localization.AtPrime p) C A 𝔪 hcomap
  have key := GlobalTheory.T.exists_mul_fst_eq_of_integral_of_conductor (AdicCompletion (maximalIdeal A) A) S' _ e _ hd
  have hed : (e (algebraMap (Localization.AtPrime p) _ d)).1 =
      algebraMap A (AdicCompletion (maximalIdeal A) A) (algebraMap C A (algebraMap _ C d)) := by
    rw [Algebra.TensorProduct.algebraMap_apply', he]
  refine ⟨algebraMap C A (algebraMap _ C d), ?_, fun c hc => ?_⟩
  · intro h0
    apply hd0
    apply hinjC
    apply IsLocalization.injective (M := 𝔪.primeCompl) (S := A) 𝔪.primeCompl_le_nonZeroDivisors
    rw [h0, map_zero, map_zero]
  · obtain ⟨s, hs⟩ := key c hc
    exact ⟨s, by rw [hs, hed]⟩

end GlobalTheory
