import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

namespace GlobalTheory.InertiaRestrict

theorem restrict_eq_one : ∀ {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (e : Ω ≃ₐ[K] AlgebraicClosure K) (L : IntermediateField K (AlgebraicClosure K)) (h : IsFiniteAbelian K L) (v : HeightOneSpectrum (𝓞 K)), IsUnramifiedIn K v L → ∀ (A : ValuationSubring Ω), Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ σ : Formalism.ConjugateSelfDual.G K Ω, σ ∈ ReciprocityTheory.Gal.Ine (F := K) A → haveI := h.isGalois; AlgEquiv.restrictNormalHom L ((e.symm.trans σ).trans e) = 1 := by
  intro K _ _ Ω _ _ _ e L h v hv A hA σ hσ
  haveI := h.isGalois
  haveI := h.finiteDimensional
  haveI : NumberField L := NumberField.of_module_finite K L
  have hint : ∀ y : 𝓞 L, e.symm ((y : L) : AlgebraicClosure K) ∈ A := by
    intro y
    have h1 : IsIntegral ℤ (e.symm ((y : L) : AlgebraicClosure K)) :=
      map_isIntegral_int ((e.symm : AlgebraicClosure K →+* Ω).comp (algebraMap L (AlgebraicClosure K)))
        y.isIntegral_coe
    obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).1 (h1.tower_top)
    rw [← ha]
    exact a.2
  let φ : 𝓞 L →+* A :=
    { toFun := fun y => ⟨e.symm ((y : L) : AlgebraicClosure K), hint y⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }
  let Q : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap φ
  have hmem : ∀ y : 𝓞 L, y ∈ Q ↔ A.valuation (e.symm ((y : L) : AlgebraicClosure K)) < 1 := fun y =>
    ValuationSubring.valuation_lt_one_iff A (φ y)
  haveI hQp : Q.IsPrime := Ideal.comap_isPrime _ _
  haveI hQo : Q.LiesOver v.asIdeal := by
    constructor
    ext x
    rw [Ideal.under, Ideal.mem_comap, hmem, ← hA x]
    have : ((algebraMap (𝓞 K) (𝓞 L) x : L) : AlgebraicClosure K) = algebraMap K (AlgebraicClosure K) (x : K) := by
      first
        | rfl
        | (rw [RingOfIntegers.algebraMap_coe]; rfl)
        | simp [IsScalarTower.algebraMap_apply K L (AlgebraicClosure K)]
    rw [this, AlgEquiv.commutes]
  have hram : Q.ramificationIdx (𝓞 K) = 1 := hv Q hQp hQo
  have hcard : Nat.card (Q.inertia (L ≃ₐ[K] L)) = 1 := by
    have : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ K L
    have hpr : (Q.under (𝓞 K)).IsPrime := Ideal.IsPrime.under _ Q
    have hc := Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) (Q.under (𝓞 K)) Q
    rwa [Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under (𝓞 K)) Q (L ≃ₐ[K] L), hram] at hc
  have hbot : Q.inertia (L ≃ₐ[K] L) = ⊥ := Subgroup.card_eq_one.1 hcard
  have hin : AlgEquiv.restrictNormalHom L ((e.symm.trans σ).trans e) ∈ Q.inertia (L ≃ₐ[K] L) := by
    refine AddSubgroup.mem_inertia.mpr fun y => ?_
    change _ ∈ Q
    rw [hmem]
    have h2 : (((AlgEquiv.restrictNormalHom L ((e.symm.trans σ).trans e) • y - y : 𝓞 L) : L) : AlgebraicClosure K)
        = e (σ (e.symm ((y : L) : AlgebraicClosure K))) - ((y : L) : AlgebraicClosure K) := by
      have h3 : ((AlgEquiv.restrictNormalHom L ((e.symm.trans σ).trans e) • y : 𝓞 L) : L) =
          AlgEquiv.restrictNormalHom L ((e.symm.trans σ).trans e) (y : L) := rfl
      simp only [map_sub, h3, AlgEquiv.restrictNormalHom_apply]
      have h4 := AlgEquiv.restrictNormalHom_apply L ((e.symm.trans σ).trans e) (y : L)
      rw [AddSubgroupClass.coe_sub, h4]
      rfl
    rw [h2, map_sub, AlgEquiv.symm_apply_apply]
    exact hσ.2 _ ((A.valuation_le_one_iff _).2 (hint y))
  rw [hbot] at hin
  exact hin

end GlobalTheory.InertiaRestrict
