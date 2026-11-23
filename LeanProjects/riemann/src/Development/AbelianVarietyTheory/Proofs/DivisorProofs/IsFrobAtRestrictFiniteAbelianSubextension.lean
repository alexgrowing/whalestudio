import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import ReciprocityTheory.ClassFieldTheory.GlobalClassField.IsFrobAtMulOfMemInertiaGroup
import ReciprocityTheory.GaloisValuations.Global
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.FrobRestrict

variable {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω]

def toOm (e : Ω ≃ₐ[K] AlgebraicClosure K) (L : IntermediateField K (AlgebraicClosure K)) : 𝓞 L →+* Ω :=
  (e.symm.toRingHom.comp L.val.toRingHom).comp (algebraMap (𝓞 L) L)

theorem toOm_apply (e : Ω ≃ₐ[K] AlgebraicClosure K) (L : IntermediateField K (AlgebraicClosure K)) (y : 𝓞 L) :
    toOm e L y = e.symm ((y : L) : AlgebraicClosure K) := rfl

theorem toOm_mem (e : Ω ≃ₐ[K] AlgebraicClosure K) (L : IntermediateField K (AlgebraicClosure K))
    (A : ValuationSubring Ω) (y : 𝓞 L) : toOm e L y ∈ A :=
  ReciprocityTheory.Gal.mem_of_isIntegral_int A ((Algebra.IsIntegral.isIntegral (R := ℤ) y).map (toOm e L).toIntAlgHom)

def toA (e : Ω ≃ₐ[K] AlgebraicClosure K) (L : IntermediateField K (AlgebraicClosure K))
    (A : ValuationSubring Ω) : 𝓞 L →+* A :=
  (toOm e L).codRestrict A (toOm_mem e L A)

def primeBelow (e : Ω ≃ₐ[K] AlgebraicClosure K) (L : IntermediateField K (AlgebraicClosure K))
    (A : ValuationSubring Ω) : Ideal (𝓞 L) :=
  Ideal.comap (toA e L A) (IsLocalRing.maximalIdeal A)

theorem mem_primeBelow (e : Ω ≃ₐ[K] AlgebraicClosure K) (L : IntermediateField K (AlgebraicClosure K))
    (A : ValuationSubring Ω) (y : 𝓞 L) : y ∈ primeBelow e L A ↔ A.valuation (toOm e L y) < 1 := by
  unfold primeBelow
  rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
  rfl

instance (e : Ω ≃ₐ[K] AlgebraicClosure K) (L : IntermediateField K (AlgebraicClosure K))
    (A : ValuationSubring Ω) : (primeBelow e L A).IsPrime := by
  unfold primeBelow; infer_instance

theorem toOm_algebraMap (e : Ω ≃ₐ[K] AlgebraicClosure K) (L : IntermediateField K (AlgebraicClosure K)) (x : 𝓞 K) :
    toOm e L (algebraMap (𝓞 K) (𝓞 L) x) = algebraMap K Ω (x : K) := by
  rw [toOm_apply]
  have h1 : (((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) : AlgebraicClosure K) = algebraMap K (AlgebraicClosure K) (x : K) := rfl
  rw [h1, AlgEquiv.commutes]

theorem liesOver_primeBelow (e : Ω ≃ₐ[K] AlgebraicClosure K) (L : IntermediateField K (AlgebraicClosure K))
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (hA : Formalism.ConjugateSelfDual.IsPlaceOver A v) :
    (primeBelow e L A).LiesOver v.asIdeal := by
  constructor
  ext x
  rw [Ideal.mem_comap, mem_primeBelow, toOm_algebraMap]
  exact (hA x).symm

theorem isFrobAt_primeBelow (e : Ω ≃ₐ[K] AlgebraicClosure K) (L : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L] [IsGalois K L]
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (hA : Formalism.ConjugateSelfDual.IsPlaceOver A v)
    (σ : Formalism.ConjugateSelfDual.G K Ω) (hσ : Formalism.ConjugateSelfDual.IsFrob (F := K) A (Formalism.ConjugateSelfDual.normV v) σ) :
    IsFrobAt K L (AlgEquiv.restrictNormalHom L ((e.symm.trans σ).trans e)) (primeBelow e L A) := by
  haveI : NumberField L := NumberField.of_module_finite K L
  haveI := liesOver_primeBelow e L A v hA
  rw [ReciprocityTheory.DiscreteGroups.GlobalClassField.isFrobAt_iff_forall]
  have hu : (primeBelow e L A).under (𝓞 K) = v.asIdeal := (Ideal.LiesOver.over).symm
  rw [hu]
  intro y
  rw [mem_primeBelow, map_sub, map_pow]
  have hy : toOm e L (AlgEquiv.restrictNormalHom L ((e.symm.trans σ).trans e) • y) = σ (toOm e L y) := by
    rw [toOm_apply, toOm_apply]
    have h2 : (((AlgEquiv.restrictNormalHom L ((e.symm.trans σ).trans e) • y : 𝓞 L) : L) : AlgebraicClosure K)
        = ((e.symm.trans σ).trans e) ((y : L) : AlgebraicClosure K) := by
      rw [← AlgEquiv.restrictNormalHom_apply]; rfl
    rw [h2]
    simp
  rw [hy]
  exact hσ.2 _ ((A.valuation_le_one_iff _).mpr (toOm_mem e L A y))

theorem isFrobAt_restrict : ∀ {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (e : Ω ≃ₐ[K] AlgebraicClosure K) (L : IntermediateField K (AlgebraicClosure K)) (h : IsFiniteAbelian K L)
    (v : HeightOneSpectrum (𝓞 K)) (A : ValuationSubring Ω), Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ σ : Formalism.ConjugateSelfDual.G K Ω,
    Formalism.ConjugateSelfDual.IsFrob (F := K) A (Formalism.ConjugateSelfDual.normV v) σ → ∀ Q : Ideal (𝓞 L), Q.IsPrime → Q.LiesOver v.asIdeal →
    haveI := h.finiteDimensional; haveI := h.isGalois;
    IsFrobAt K L (AlgEquiv.restrictNormalHom L ((e.symm.trans σ).trans e)) Q := by
  intro K _ _ Ω _ _ _ e L h v A hA σ hσ Q hQ hQv
  haveI := h.finiteDimensional
  haveI := h.isGalois
  haveI : NumberField L := NumberField.of_module_finite K L
  haveI := liesOver_primeBelow e L A v hA
  exact ReciprocityTheory.DiscreteGroups.GlobalClassField.isFrobAt_of_comm v (primeBelow e L A) Q h.comm _ (isFrobAt_primeBelow e L A v hA σ hσ)

end GlobalTheory.FrobRestrict
