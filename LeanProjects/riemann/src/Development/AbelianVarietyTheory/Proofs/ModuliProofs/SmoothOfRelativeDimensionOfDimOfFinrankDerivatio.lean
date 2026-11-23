import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SmoothTangent

theorem exists_section_of_ker_sq_eq_bot {k B F : Type*} [CommRing k] [CommRing B] [CommRing F]
    [Algebra k B] [Algebra k F] [Algebra.FormallySmooth k F] (π : B →ₐ[k] F)
    (hπ : Function.Surjective π) (h : RingHom.ker π.toRingHom ^ 2 = ⊥) :
    ∃ g : F →ₐ[k] B, π.comp g = AlgHom.id k F :=
  ⟨_, Algebra.FormallySmooth.comp_liftOfSurjective (AlgHom.id k F) π hπ ⟨2, h⟩⟩

theorem kerCotangentToTensor_injective (k R F : Type*) [CommRing k] [CommRing R] [CommRing F]
    [Algebra k R] [Algebra k F] [Algebra R F] [IsScalarTower k R F] [Algebra.FormallySmooth k F]
    (hs : Function.Surjective (algebraMap R F)) :
    Function.Injective (KaehlerDifferential.kerCotangentToTensor k R F) := by
  have hsurj : Function.Surjective (IsScalarTower.toAlgHom k R F).kerSquareLift :=
    fun x ↦ by
      obtain ⟨y, rfl⟩ := hs x
      exact ⟨Ideal.Quotient.mk _ y, rfl⟩
  have hnil : RingHom.ker (IsScalarTower.toAlgHom k R F).kerSquareLift.toRingHom ^ 2 = ⊥ := by
    rw [AlgHom.ker_kerSquareLift, Ideal.cotangentIdeal_square]
  obtain ⟨g, hg⟩ := exists_section_of_ker_sq_eq_bot _ hsurj hnil
  obtain ⟨l, hl⟩ := (retractionKerCotangentToTensorEquivSection (R := k) hs).symm ⟨g, hg⟩
  exact Function.LeftInverse.injective (g := l) fun x ↦ congr($hl x)

noncomputable def derivationEquivDual (k R C : Type*) [CommRing k] [CommRing R] [CommRing C]
    [Algebra k R] [Algebra k C] [Algebra R C] [IsScalarTower k R C] :
    Derivation k R C ≃ₗ[C] Module.Dual C (C ⊗[R] Ω[R⁄k]) :=
  (({ (KaehlerDifferential.linearMapEquivDerivation k R (M := C)).toAddEquiv with
      map_smul' := fun _ _ ↦ rfl } : (Ω[R⁄k] →ₗ[R] C) ≃ₗ[C] Derivation k R C).symm).trans
    (LinearMap.liftBaseChangeEquiv C)

theorem finrank_cotangent_le_finrank_derivation (k : Type*) [Field k] [PerfectField k]
    {R : Type*} [CommRing R] [Algebra k R] [Algebra.FiniteType k R] (m : Ideal R) [m.IsMaximal]
    (C : Type*) [Field C] [Algebra k C] [Algebra R C] [IsScalarTower k R C]
    [Algebra (R ⧸ m) C] [IsScalarTower R (R ⧸ m) C] :
    Module.finrank (R ⧸ m) m.Cotangent ≤ Module.finrank C (Derivation k R C) := by
  let := Ideal.Quotient.field m
  have : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing _ _
  have : Algebra.FormallyEtale k (R ⧸ m) := Algebra.FormallyEtale.of_isSeparable k _
  have hs : Function.Surjective (algebraMap R (R ⧸ m)) := Ideal.Quotient.mk_surjective
  have hinj := kerCotangentToTensor_injective k R (R ⧸ m) hs
  let e : m.Cotangent →ₗ[R] (R ⧸ m) ⊗[R] Ω[R⁄k] :=
    KaehlerDifferential.kerCotangentToTensor k R (R ⧸ m) ∘ₗ
      (Ideal.Cotangent.equivOfEq _ _ Ideal.mk_ker.symm).toLinearMap
  have he : Function.Injective (e.extendScalarsOfSurjective hs) :=
    hinj.comp (Ideal.Cotangent.equivOfEq _ _ Ideal.mk_ker.symm).injective
  rw [(derivationEquivDual k R C).finrank_eq, Subspace.dual_finrank_eq,
    ← (TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ m) C C Ω[R⁄k]).finrank_eq,
    Module.finrank_baseChange]
  exact LinearMap.finrank_le_finrank_of_injective he

theorem le_height_of_forall_minimalPrimes (k : Type) [Field k] {R : Type} [CommRing R]
    [Algebra k R] [Algebra.FiniteType k R] {d : ℕ}
    (hd : ∀ q ∈ minimalPrimes R, (d : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ q))
    (m : Ideal R) [m.IsMaximal] : (d : ℕ∞) ≤ m.height := by
  obtain ⟨p, hp, hpm⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ m)
  have := hp.1.1
  obtain ⟨n, h₁, h₂⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq k (R ⧸ p)
  have hdn : (d : ℕ∞) ≤ n := by
    have := hd p hp
    rw [h₁] at this
    exact_mod_cast this
  have hψ : Function.Surjective (Ideal.Quotient.mk p) := Ideal.Quotient.mk_surjective
  have hcm : (m.map (Ideal.Quotient.mk p)).comap (Ideal.Quotient.mk p) = m := by
    rw [Ideal.comap_map_of_surjective _ hψ, sup_eq_left]
    exact Ideal.mk_ker.le.trans hpm
  have : (m.map (Ideal.Quotient.mk p)).IsMaximal := by
    refine (Ideal.map_eq_top_or_isMaximal_of_surjective _ hψ inferInstance).resolve_left fun h ↦ ?_
    rw [h, Ideal.comap_top] at hcm
    exact Ideal.IsMaximal.ne_top inferInstance hcm.symm
  have h := height_le_height_comap_of_surjective _ hψ (m.map (Ideal.Quotient.mk p))
  rw [hcm, ReciprocityTheory.CA.height_eq_of_isMaximal_of_trdeg_eq_field n h₂] at h
  exact hdn.trans h

end GlobalTheory.SmoothTangent

namespace GlobalTheory

open SmoothTangent

theorem smoothOfRelativeDimension_of_dim_of_finrank_derivation_le :
    ∀ (k : Type) [Field k] [CharZero k] (e : k →+* ℂ) (R : Type) [CommRing R] [Algebra k R] (d : ℕ),
      Algebra.FiniteType k R →
      (∀ q ∈ minimalPrimes R, (d : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ q)) →
      (∀ [Algebra k ℂ] [Algebra R ℂ] [IsScalarTower k R ℂ], algebraMap k ℂ = e →
        Module.finrank ℂ (Derivation k R ℂ) ≤ d) →
      SmoothOfRelativeDimension d (spMap (algebraMap k R)) := by
  intro k _ _ e R _ _ d _ hd ht
  have : Algebra.FinitePresentation k R := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have key (m : Ideal R) (hm : m.IsMaximal) :
      ∃ f ∉ m, Algebra.IsStandardSmoothOfRelativeDimension d k (Localization.Away f) := by
    have h₁ : (d : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime m) := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m)]
      exact_mod_cast le_height_of_forall_minimalPrimes k hd m
    have h₂ : Module.finrank (R ⧸ m) m.Cotangent ≤ d := by
      let := Ideal.Quotient.field m
      have : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing _ _
      let : Algebra k ℂ := e.toAlgebra
      let φ : (R ⧸ m) →ₐ[k] ℂ := IsAlgClosed.lift
      let : Algebra (R ⧸ m) ℂ := φ.toRingHom.toAlgebra
      let : Algebra R ℂ := (φ.toRingHom.comp (Ideal.Quotient.mk m)).toAlgebra
      have : IsScalarTower R (R ⧸ m) ℂ := .of_algebraMap_eq fun _ ↦ rfl
      have : IsScalarTower k R ℂ := .of_algebraMap_eq fun x ↦ (φ.commutes x).symm
      exact (finrank_cotangent_le_finrank_derivation k m ℂ).trans (ht rfl)
    obtain ⟨-, -, -, h₃, -, h₄⟩ := isSmoothAt_of_finrank_cotangent_le_of_perfectField k m h₁ h₂
    exact exists_isStandardSmoothOfRelativeDimension_of_isSmoothAt k m h₄
  refine (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension d)).mpr ?_
  refine ⟨{f | Algebra.IsStandardSmoothOfRelativeDimension d k (Localization.Away f)}, ?_, ?_⟩
  · by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨f, hf, hs⟩ := key m hm
    exact hf (hle (Ideal.subset_span hs))
  · intro f hf
    have := (RingHom.isStandardSmoothOfRelativeDimension_algebraMap d).mpr hf
    rwa [IsScalarTower.algebraMap_eq k R] at this

end GlobalTheory
