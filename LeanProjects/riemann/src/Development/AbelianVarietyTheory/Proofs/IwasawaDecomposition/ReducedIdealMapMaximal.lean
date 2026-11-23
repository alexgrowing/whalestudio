import Mathlib
open IsLocalRing

namespace GlobalTheory

theorem exists_mul_mem_of_isRadical_of_minimal {B : Type} [CommRing B] (P J : Ideal B) [P.IsPrime]
    (hrad : J.IsRadical) (hmin : ∀ P' : Ideal B, P'.IsPrime → J ≤ P' → P' ≤ P → P' = P)
    (x : B) (hx : x ∈ P) : ∃ s ∉ P, s * x ∈ J := by
  by_contra hcon
  push_neg at hcon
  let M : Submonoid B := P.primeCompl ⊔ Submonoid.powers x
  have hdisj : Disjoint (J : Set B) M := by
    rw [Set.disjoint_left]
    intro y hyJ hyM
    obtain ⟨a, ha, b, hb, rfl⟩ := Submonoid.mem_sup.1 hyM
    obtain ⟨n, rfl⟩ := hb
    apply hcon a ha
    apply hrad
    refine ⟨n + 1, ?_⟩
    have : (a * x) ^ (n + 1) = (a ^ n * x) * (a * x ^ n) := by ring
    rw [this]
    exact J.mul_mem_left _ hyJ
  obtain ⟨P', hP', hJP', hdisj'⟩ := Ideal.exists_le_prime_disjoint J M hdisj
  have hle : P' ≤ P := by
    intro y hy
    by_contra hyP
    exact Set.disjoint_left.1 hdisj' hy (Submonoid.mem_sup_left (show y ∈ P.primeCompl from hyP))
  have hPP := hmin P' hP' hJP' hle
  subst hPP
  exact Set.disjoint_left.1 hdisj' hx (Submonoid.mem_sup_right (Submonoid.mem_powers x))

theorem comap_map_eq_maximalIdeal_of_finite_formallyUnramified {B R : Type} [CommRing B] [CommRing R]
    (ψ : B →+* R) (hf : ψ.Finite) (hu : ψ.FormallyUnramified) (Q : Ideal R) [Q.IsPrime] :
    (Q.comap ψ).map ((algebraMap R (Localization.AtPrime Q)).comp ψ) =
      maximalIdeal (Localization.AtPrime Q) := by
  algebraize [ψ]
  haveI hQ' : (Q.comap ψ).IsPrime := Ideal.comap_isPrime ψ Q
  letI : Algebra (Localization.AtPrime (Q.comap ψ)) (Localization.AtPrime Q) :=
    (Localization.localRingHom (Q.comap ψ) Q ψ rfl).toAlgebra
  have hcomp : (algebraMap (Localization.AtPrime (Q.comap ψ)) (Localization.AtPrime Q)).comp
      (algebraMap B (Localization.AtPrime (Q.comap ψ))) = (algebraMap R (Localization.AtPrime Q)).comp ψ := by
    ext b
    simp [RingHom.algebraMap_toAlgebra, Localization.localRingHom_to_map]
  haveI : IsScalarTower B (Localization.AtPrime (Q.comap ψ)) (Localization.AtPrime Q) :=
    IsScalarTower.of_algebraMap_eq (fun b => (RingHom.congr_fun hcomp b).symm)
  haveI : Algebra.FormallyUnramified B R := hu
  haveI : Algebra.FormallyUnramified B (Localization.AtPrime Q) := Algebra.FormallyUnramified.comp B R _
  haveI : Algebra.FormallyUnramified (Localization.AtPrime (Q.comap ψ)) (Localization.AtPrime Q) :=
    .of_restrictScalars B _ _
  haveI : Module.Finite B R := hf
  haveI : Algebra.EssFiniteType B (Localization.AtPrime Q) := .comp B R _
  haveI : Algebra.EssFiniteType (Localization.AtPrime (Q.comap ψ)) (Localization.AtPrime Q) := .of_comp B _ _
  haveI : IsLocalHom (algebraMap (Localization.AtPrime (Q.comap ψ)) (Localization.AtPrime Q)) := by
    rw [RingHom.algebraMap_toAlgebra]; infer_instance
  have h := Algebra.FormallyUnramified.map_maximalIdeal (R := Localization.AtPrime (Q.comap ψ))
    (S := Localization.AtPrime Q)
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, hcomp] at h
  exact h

theorem map_eq_maximalIdeal_of_reduced_minimal :
    ∀ {B R : Type} [CommRing B] [CommRing R] (ψ : B →+* R),
    ψ.Finite → ψ.FormallyUnramified → ∀ (Q : Ideal R) [Q.IsPrime] (J : Ideal B), J ≤ Q.comap ψ →
    IsReduced (B ⧸ J) → (∀ P : Ideal B, P.IsPrime → J ≤ P → P ≤ Q.comap ψ → P = Q.comap ψ) →
    J.map ((algebraMap R (Localization.AtPrime Q)).comp ψ) = maximalIdeal (Localization.AtPrime Q) := by
  intro B R _ _ ψ hf hu Q _ J hJ hred hmin
  rw [← comap_map_eq_maximalIdeal_of_finite_formallyUnramified ψ hf hu Q]
  apply le_antisymm (Ideal.map_mono hJ)
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  haveI : (Q.comap ψ).IsPrime := Ideal.comap_isPrime ψ Q
  obtain ⟨s, hs, hsx⟩ := exists_mul_mem_of_isRadical_of_minimal (Q.comap ψ) J
    ((Ideal.isRadical_iff_quotient_reduced J).2 hred) hmin x hx
  have hunit : IsUnit (((algebraMap R (Localization.AtPrime Q)).comp ψ) s) :=
    IsLocalization.map_units (Localization.AtPrime Q) (⟨ψ s, hs⟩ : Q.primeCompl)
  have hmem := Ideal.mem_map_of_mem ((algebraMap R (Localization.AtPrime Q)).comp ψ) hsx
  rw [map_mul] at hmem
  exact Ideal.mem_comap.2 ((Ideal.unit_mul_mem_iff_mem _ hunit).1 hmem)

end GlobalTheory
