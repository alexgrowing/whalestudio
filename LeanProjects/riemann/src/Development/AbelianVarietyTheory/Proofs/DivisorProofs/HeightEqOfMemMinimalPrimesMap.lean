import Mathlib
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightMaximalLePrimeAddDim

namespace GlobalTheory.FieldExtHeight

open ReciprocityTheory.CA TensorProduct

theorem height_eq_of_mem_minimalPrimes_map {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S] (𝔭 : Ideal R) [𝔭.IsPrime]
    (Q : Ideal S) (hQ : Q ∈ (𝔭.map (algebraMap R S)).minimalPrimes) :
    Q.height = 𝔭.height := by
  have hQp : Q.IsPrime := hQ.1.1
  have hc : Q.comap (algebraMap R S) = 𝔭 := by
    have hle : Ideal.map (algebraMap R S) 𝔭 ≤ Q := hQ.1.2
    set q := Q.comap (algebraMap R S) with hq
    have : q.IsPrime := Ideal.comap_isPrime _ _
    have : Q.LiesOver q := ⟨rfl⟩
    have hpq : 𝔭 ≤ q := Ideal.map_le_iff_le_comap.mp hle
    obtain ⟨P, hPQ, hP, hPl⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := 𝔭) Q hpq
    have hPext : Ideal.map (algebraMap R S) 𝔭 ≤ P := by
      rw [Ideal.map_le_iff_le_comap]
      exact hPl.over.le
    have hQP : Q ≤ P := hQ.2 ⟨hP, hPext⟩ hPQ
    have hPQe : P = Q := le_antisymm hPQ hQP
    subst hPQe
    exact hPl.over.symm
  have : Q.LiesOver 𝔭 := ⟨hc.symm⟩
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown 𝔭 Q]
  have h0 : (Q.map (Ideal.Quotient.mk (𝔭.map (algebraMap R S)))).height = 0 := by
    have hQ' := hQ
    rw [Ideal.minimalPrimes_eq_comap] at hQ'
    obtain ⟨Q', hQ'm, hQ'e⟩ := hQ'
    have : Q'.IsPrime := hQ'm.1.1
    rw [← hQ'e, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    exact Ideal.height_eq_zero_iff.mpr hQ'm
  rw [h0, add_zero]

theorem height_map_mk_ker {R A : Type*} [CommRing R] [CommRing A] (π : R →+* A)
    (hπ : Function.Surjective π) (q : Ideal A) :
    ((q.comap π).map (Ideal.Quotient.mk (RingHom.ker π))).height = q.height := by
  let e := RingHom.quotientKerEquivOfSurjective hπ
  have h : (q.comap π).map (Ideal.Quotient.mk (RingHom.ker π)) = q.comap e := by
    have h1 : q.comap π = (q.comap e).comap (Ideal.Quotient.mk (RingHom.ker π)) := by
      ext x; rfl
    rw [h1, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  rw [h, RingEquiv.height_comap]

theorem height_comap_le_one {R S A B : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S] [IsDomain A]
    (π : R →+* A) (ψ : S →+* B) (ι : A →+* B) (hπ : Function.Surjective π)
    (hψ : Function.Surjective ψ) (hcomm : ψ.comp (algebraMap R S) = ι.comp π)
    (hker : RingHom.ker ψ = (RingHom.ker π).map (algebraMap R S))
    (hCM : ∀ (𝔔 : Ideal S) [𝔔.IsPrime], IsCM (Localization.AtPrime 𝔔))
    (P Q : Ideal B) (f : B) (hP : P ∈ minimalPrimes B)
    (hQ : Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes) : (Q.comap ι).height ≤ 1 := by
  haveI hpp : (RingHom.ker π).IsPrime := RingHom.ker_isPrime π
  haveI : P.IsPrime := hP.1.1
  haveI : Q.IsPrime := hQ.1.1
  have hP' : P.comap ψ ∈ ((RingHom.ker π).map (algebraMap R S)).minimalPrimes := by
    rw [← hker, RingHom.ker_eq_comap_bot]
    exact Ideal.minimalPrimes_comap_of_surjective hψ hP
  obtain ⟨g, rfl⟩ := hψ f
  have hQ' : Q.comap ψ ∈ (P.comap ψ ⊔ Ideal.span {g}).minimalPrimes := by
    have h1 := Ideal.minimalPrimes_comap_of_surjective hψ hQ
    have h2 : (P ⊔ Ideal.span {ψ g}).comap ψ = P.comap ψ ⊔ Ideal.span {g} := by
      have h3 : P ⊔ Ideal.span {ψ g} = (P.comap ψ ⊔ Ideal.span {g}).map ψ := by
        rw [Ideal.map_sup, Ideal.map_comap_of_surjective _ hψ, Ideal.map_span,
          Set.image_singleton]
      rw [h3, Ideal.comap_map_of_surjective _ hψ]
      exact sup_eq_left.mpr (le_sup_of_le_left (Ideal.comap_mono bot_le))
    rwa [h2] at h1
  have e1 := height_eq_of_mem_minimalPrimes_map _ _ hP'
  have e2 := Ideal.map_height_le_one_of_mem_minimalPrimes hQ'
  have hle : P.comap ψ ≤ Q.comap ψ := le_sup_left.trans hQ'.1.2
  have e3 := height_eq_add_of_isCM_localization (Q.comap ψ) (P.comap ψ) (hCM _) hle
  have hq : (Q.comap ψ).comap (algebraMap R S) = (Q.comap ι).comap π := by
    rw [Ideal.comap_comap, Ideal.comap_comap, hcomm]
  haveI : (Q.comap ψ).LiesOver ((Q.comap ι).comap π) := ⟨hq.symm⟩
  have e4 := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown ((Q.comap ι).comap π)
    (Q.comap ψ)
  have e5 := height_add_height_map_quotient_le (RingHom.ker π) ((Q.comap ι).comap π)
    (Ideal.comap_mono bot_le)
  rw [height_map_mk_ker π hπ] at e5
  have hfin : (RingHom.ker π).height ≠ ⊤ := Ideal.height_ne_top hpp.ne_top
  have key : (RingHom.ker π).height + (Q.comap ι).height ≤ (RingHom.ker π).height + 1 := by
    calc _ ≤ ((Q.comap ι).comap π).height := e5
      _ ≤ (Q.comap ψ).height := by rw [e4]; exact le_self_add
      _ ≤ _ := by rw [e3, e1]; exact add_le_add le_rfl e2
  exact (ENat.add_le_add_iff_left hfin).mp key

attribute [local instance] MvPolynomial.algebraMvPolynomial

end GlobalTheory.FieldExtHeight
