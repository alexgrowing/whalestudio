import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.OneAlg
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MainFin

set_option linter.overlappingInstances false

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

namespace UpperTheory.V.J.ChevalleyRestriction

private theorem ext_integral (R S : Type) [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S))
    (K : Type) [Field K] [IsAlgClosed K] (y : R →+* K) :
    ∃ ξ : S →+* K, ξ.comp (algebraMap R S) = y := by
  classical
  haveI hP : (RingHom.ker y).IsPrime := RingHom.ker_isPrime y
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker y)
    (⊥ : Ideal S) (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
  let y' : (R ⧸ Ideal.comap (algebraMap R S) Q) →+* K :=
    Ideal.Quotient.lift _ y (fun a ha => by rw [hQc] at ha; exact ha)
  have hy' : Function.Injective y' := by
    refine (injective_iff_map_eq_zero y').2 fun z hz => ?_
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
    rw [hQc]
    exact hz
  letI : Algebra (R ⧸ Ideal.comap (algebraMap R S) Q) K := y'.toAlgebra
  haveI : IsDomain (R ⧸ Ideal.comap (algebraMap R S) Q) := by
    rw [hQc]; infer_instance
  haveI : Module.IsTorsionFree (R ⧸ Ideal.comap (algebraMap R S) Q) K :=
    Module.isTorsionFree_iff_algebraMap_injective.2 hy'
  haveI : Module.IsTorsionFree (R ⧸ Ideal.comap (algebraMap R S) Q) (S ⧸ Q) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 Ideal.algebraMap_quotient_injective
  haveI : Nontrivial (R ⧸ Ideal.comap (algebraMap R S) Q) := IsDomain.toNontrivial
  haveI hI : Algebra.IsIntegral (R ⧸ Ideal.comap (algebraMap R S) Q) (S ⧸ Q) :=
    Algebra.IsIntegral.quotient
  haveI : Algebra.IsAlgebraic (R ⧸ Ideal.comap (algebraMap R S) Q) (S ⧸ Q) :=
    Algebra.IsIntegral.isAlgebraic
  let φ : (S ⧸ Q) →ₐ[R ⧸ Ideal.comap (algebraMap R S) Q] K := IsAlgClosed.lift
  refine ⟨(φ : (S ⧸ Q) →+* K).comp (Ideal.Quotient.mk Q), ?_⟩
  ext r
  have h := φ.commutes (Ideal.Quotient.mk _ r)
  exact h

private theorem one_tr (R S : Type) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S]
    (x : S) (hx : Function.Surjective (Polynomial.aeval x : Polynomial R →ₐ[R] S))
    (ht : Transcendental R x) (c : S) (hc : c ≠ 0) :
    ∃ b : R, b ≠ 0 ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (y : R →+* K), y b ≠ 0 →
      ∃ ξ : S →+* K, ξ.comp (algebraMap R S) = y ∧ ξ c ≠ 0 := by
  classical
  have hinjx := transcendental_iff_injective.1 ht
  let e : Polynomial R ≃ₐ[R] S := AlgEquiv.ofBijective (Polynomial.aeval x) ⟨hinjx, hx⟩
  obtain ⟨p, rfl⟩ := hx c
  have hp : p ≠ 0 := by
    rintro rfl
    simp at hc
  refine ⟨p.leadingCoeff, Polynomial.leadingCoeff_ne_zero.2 hp, ?_⟩
  intro K _ _ y hy
  have hmap : p.map y ≠ 0 := fun h => hy (by
    have := congrArg (fun q => Polynomial.coeff q p.natDegree) h
    simpa using this)
  have hcard : ((p.map y).natDegree : Cardinal) < Cardinal.mk K :=
    (Cardinal.natCast_lt_aleph0).trans_le (Cardinal.aleph0_le_mk K)
  obtain ⟨t, htt⟩ := Polynomial.exists_eval_ne_zero_of_natDegree_lt_card _ hmap hcard
  refine ⟨(Polynomial.eval₂RingHom y t).comp (e.symm : S →+* Polynomial R), ?_, ?_⟩
  · ext r
    have h1 : e.symm (algebraMap R S r) = Polynomial.C r := by
      have := e.symm.commutes r
      simpa [Polynomial.algebraMap_eq] using this
    simp [h1]
  · have h2 : e.symm (Polynomial.aeval x p) = p := e.symm_apply_apply p
    simpa [h2, Polynomial.eval_map] using htt

private theorem isAlg_aeval (R S : Type) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Algebra R S] (x : S) (hxa : IsAlgebraic R x) (p : Polynomial R) :
    IsAlgebraic R (Polynomial.aeval x p) := by
  haveI : Nontrivial R := IsDomain.toNontrivial
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa using hp.add hq
  | monomial n r =>
    rw [Polynomial.aeval_monomial]
    exact (isAlgebraic_algebraMap r).mul (hxa.pow n)

private theorem one_alg (R S : Type) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S]
    (hinj : Function.Injective (algebraMap R S))
    (x : S) (hx : Function.Surjective (Polynomial.aeval x : Polynomial R →ₐ[R] S))
    (hxa : IsAlgebraic R x) (c : S) (hc : c ≠ 0) :
    ∃ b : R, b ≠ 0 ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (y : R →+* K), y b ≠ 0 →
      ∃ ξ : S →+* K, ξ.comp (algebraMap R S) = y ∧ ξ c ≠ 0 :=
  _root_.UpperTheory.Reformulated.B.Ra3.one_alg R S hinj x hx hxa c hc

private theorem one (R S : Type) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S]
    (hinj : Function.Injective (algebraMap R S))
    (x : S) (hx : Function.Surjective (Polynomial.aeval x : Polynomial R →ₐ[R] S))
    (c : S) (hc : c ≠ 0) :
    ∃ b : R, b ≠ 0 ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (y : R →+* K), y b ≠ 0 →
      ∃ ξ : S →+* K, ξ.comp (algebraMap R S) = y ∧ ξ c ≠ 0 := by
  by_cases h : IsAlgebraic R x
  · exact one_alg R S hinj x hx h c hc
  · exact one_tr R S x hx h c hc

private theorem main_fin (A : Type) [CommRing A] [IsDomain A] (s : Finset A) :
    ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra B A],
      Algebra.adjoin B (s : Set A) = ⊤ → Function.Injective (algebraMap B A) →
      ∀ a : A, a ≠ 0 → ∃ b : B, b ≠ 0 ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (y : B →+* K),
        y b ≠ 0 → ∃ ξ : A →+* K, ξ.comp (algebraMap B A) = y ∧ ξ a ≠ 0 :=
  _root_.UpperTheory.Reformulated.B.Ra5.main_fin A s

end UpperTheory.V.J.ChevalleyRestriction

theorem UpperTheory.V.J.chev :
    ∀ (B A : Type) [CommRing B] [IsDomain B] [CommRing A] [IsDomain A] [Algebra B A] [Algebra.FiniteType B A], Function.Injective (algebraMap B A) →
        ∀ a : A, a ≠ 0 → ∃ b : B, b ≠ 0 ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (y : B →+* K), y b ≠ 0 →
          ∃ ξ : A →+* K, ξ.comp (algebraMap B A) = y ∧ ξ a ≠ 0 := by
  intro B A _ _ _ _ _ hft hinj a ha
  obtain ⟨s, hs⟩ := hft.out
  exact UpperTheory.V.J.ChevalleyRestriction.main_fin A s B hs hinj a ha
