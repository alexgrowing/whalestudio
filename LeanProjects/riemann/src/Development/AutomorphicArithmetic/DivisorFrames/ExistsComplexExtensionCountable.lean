import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ValCount
open IsLocalRing NumberField IsDedekindDomain GlobalTheory.ValCount
open scoped Classical

private theorem UpperTheory.nonempty_algHom_complex_countable (R K : Type) [CommRing R] [IsDomain R] [Countable R]
    [Field K] [Countable K] [Algebra R K] [Algebra R ℂ] [FaithfulSMul R K] [FaithfulSMul R ℂ] :
    Nonempty (K →ₐ[R] ℂ) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis R ℂ
  have hC : Cardinal.aleph0 < Cardinal.mk ℂ := by
    rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum
  have hct := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht
    Cardinal.mk_le_aleph0 hC
  have hle : Cardinal.mk s ≤ Cardinal.mk t :=
    le_trans Cardinal.mk_le_aleph0 (hct ▸ hC.le)
  obtain ⟨e⟩ := (Cardinal.le_def _ _).1 hle
  have hw : AlgebraicIndependent R (((↑) : t → ℂ) ∘ e) := ht.1.comp e e.injective
  let S := Algebra.adjoin R (Set.range ((↑) : s → K))
  let φ : S →ₐ[R] ℂ :=
    (MvPolynomial.aeval (((↑) : t → ℂ) ∘ e)).comp hs.1.aevalEquiv.symm.toAlgHom
  have hφ : Function.Injective φ :=
    (algebraicIndependent_iff_injective_aeval.1 hw).comp hs.1.aevalEquiv.symm.injective
  let : Algebra S ℂ := φ.toRingHom.toAlgebra
  have : IsScalarTower R S ℂ := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  have : FaithfulSMul S ℂ := (faithfulSMul_iff_algebraMap_injective S ℂ).2 hφ
  have : Algebra.IsAlgebraic S K := hs.isAlgebraic
  exact ⟨(IsAlgClosed.lift : K →ₐ[S] ℂ).restrictScalars R⟩

theorem UpperTheory.exists_complex_extension_countable :
    ∀ (K L : Type) [Field K] [Field L] [Countable L] (φ : K →+* L) (ι : K →+* ℂ), ∃ q : L →+* ℂ, q.comp φ = ι := by
  intro K L _ _ _ φ ι
  have hc : Countable K := φ.injective.countable
  let : Algebra K L := φ.toAlgebra
  let : Algebra K ℂ := ι.toAlgebra
  obtain ⟨j⟩ := UpperTheory.nonempty_algHom_complex_countable K L
  exact ⟨j.toRingHom, j.comp_algebraMap⟩
