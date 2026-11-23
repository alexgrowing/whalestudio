import Mathlib
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemZpowersOfTameGen
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongOfCongOnFixed
open NumberField IsDedekindDomain

namespace GlobalTheory.TameRootSurj

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

theorem irreducible_X_pow_sub_C {E : Type} [Field E] [NumberField E]
    (P : HeightOneSpectrum (𝓞 E)) {L : ℕ} (hL : 0 < L) {ϖ : 𝓞 E}
    (hmem : ϖ ∈ P.asIdeal) (hnot : ϖ ∉ P.asIdeal ^ 2) :
    Irreducible (X ^ L - C (ϖ : E)) := by
  have hmon : (X ^ L - C ϖ : (𝓞 E)[X]).Monic := monic_X_pow_sub_C ϖ hL.ne'
  have hdeg : (X ^ L - C ϖ : (𝓞 E)[X]).natDegree = L := natDegree_X_pow_sub_C
  have hEis : (X ^ L - C ϖ : (𝓞 E)[X]).IsEisensteinAt P.asIdeal := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hmon.leadingCoeff]; exact fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
    · intro m hm
      rw [hdeg] at hm
      rw [coeff_sub, coeff_X_pow, coeff_C, if_neg hm.ne]
      by_cases h0 : m = 0
      · subst h0; simpa using P.asIdeal.neg_mem_iff.2 hmem
      · simp [h0]
    · rw [coeff_sub, coeff_X_pow, coeff_C, if_neg hL.ne, if_pos rfl, zero_sub]
      rwa [Ideal.neg_mem_iff]
  have hirr : Irreducible (X ^ L - C ϖ : (𝓞 E)[X]) :=
    hEis.irreducible P.isPrime hmon.isPrimitive (by rw [hdeg]; exact hL)
  have hmap : (X ^ L - C ϖ : (𝓞 E)[X]).map (algebraMap (𝓞 E) E) = X ^ L - C (ϖ : E) := by
    simp [Polynomial.map_sub]
  rw [← hmap]; exact (hmon.irreducible_iff_irreducible_map_fraction_map (K := E)).1 hirr

theorem main : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (L : ℕ) (ϖ : 𝓞 E) (π : Ω),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → ((L : ℕ) : 𝓞 E) ∉ P.asIdeal → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    π ^ L = algebraMap E Ω (ϖ : E) → ∃ σ ∈ ReciprocityTheory.Gal.Ine (F := E) A, IsPrimitiveRoot (σ π / π) L := by
  intro E Ω _ _ _ _ _ P A L ϖ π hA hL h1 h2 hπ
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; exact h2 (zero_mem _)
  have hL0 : L ≠ 0 := by rintro rfl; exact hL (by simp)
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hL0, eq_comm, map_eq_zero] at hπ
    exact hϖ0 (by simpa using hπ)
  rcases Nat.lt_or_ge L 2 with hL2 | hL2
  · have hL1 : L = 1 := by omega
    subst hL1
    refine ⟨1, one_mem _, ?_⟩
    rw [AlgEquiv.one_apply, div_self hπ0]
    exact IsPrimitiveRoot.one
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : NeZero ((L : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hL0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω L
  have hirr := irreducible_X_pow_sub_C P (Nat.pos_of_ne_zero hL0) h1 h2
  have hmon : (X ^ L - C (ϖ : E)).Monic := monic_X_pow_sub_C _ hL0
  have hr1 : aeval π (X ^ L - C (ϖ : E)) = 0 := by simp [hπ]
  have hr2 : aeval (ζ * π) (X ^ L - C (ϖ : E)) = 0 := by simp [mul_pow, hζ.pow_eq_one, hπ]
  have hm1 := minpoly.eq_of_irreducible_of_monic hirr hr1 hmon
  have hm2 := minpoly.eq_of_irreducible_of_monic hirr hr2 hmon
  haveI : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  obtain ⟨g, hg⟩ : ∃ g : Ω ≃ₐ[E] Ω, g π = ζ * π := by
    obtain ⟨g, hg⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := E) (E := Ω)).1 (hm2.symm.trans hm1)
    exact ⟨g, hg⟩
  obtain ⟨-, hx2⟩ := GlobalTheory.InertiaMovesRoot.cong_on_adjoin hA hL2 h1 h2 hπ
  letI : TopologicalSpace (IntCl E Ω) := ⊥
  haveI : DiscreteTopology (IntCl E Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl E Ω
  let H := MulAction.stabilizer (Ω ≃ₐ[E] Ω) π
  have hH : IsClosed (H : Set (Ω ≃ₐ[E] Ω)) :=
    H.isClosed_of_isOpen (stabilizer_isOpen_of_isIntegral (K := E) π)
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  obtain ⟨k, hk, k', hk', hc⟩ := GlobalTheory.InertiaMovesRoot.exists_cong_of_cong_on_fixed (R := 𝓞 E) H
    (primeBelow (F := E) A) g (fun b hb => by
      refine hx2 g b ?_ (valuation_le_one_intCl A b)
      rw [← InfiniteGalois.fixedField_fixingSubgroup (IntermediateField.adjoin E {π}),
        IntermediateField.mem_fixedField_iff]
      intro f hf
      exact congrArg Subtype.val (hb f (hf ⟨π, IntermediateField.mem_adjoin_simple_self E π⟩)))
  refine ⟨k' * g * k, GlobalTheory.InertiaMovesRoot.mem_Ine_of_cong hc, ?_⟩
  have e1 : k π = π := hk
  have e2 : k' π = π := hk'
  have e3 : (k' * g * k) π / π = k' ζ := by
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, e1, hg, map_mul, e2, mul_div_cancel_right₀ _ hπ0]
  rw [e3]
  exact hζ.map_of_injective k'.injective

end GlobalTheory.TameRootSurj
