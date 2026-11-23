import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RayFieldTheta
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingOfIntegersSqrtNegThreeModFour
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmCurveTorsionDefinedOverOfWeberValues
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberInvariantTorsionValuesSubsetOfContainsRayFiStatement

set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.WeberTransport

theorem absNorm_comap {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] (e : 𝓞 K ≃+* 𝓞 K')
    (I : Ideal (𝓞 K')) : Ideal.absNorm (I.comap e) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (Ideal.quotientEquiv (I.comap e) I e
    (Ideal.map_comap_of_surjective _ e.surjective I).symm).toEquiv

theorem containsRayField_congr {K L K' L' : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Field K'] [NumberField K'] [Field L'] [NumberField L'] (φ : K →+* L) (φ' : K' →+* L') (eK : K ≃+* K') (eL : L ≃+* L')
    (hc : ∀ x, φ' (eK x) = eL (φ x)) (n : ℕ) (h : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField φ n) :
    GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField φ' n := by
  intro P hP
  let oK := RingOfIntegers.mapRingEquiv eK
  let oL := RingOfIntegers.mapRingEquiv eL
  let Q : HeightOneSpectrum (𝓞 L) := (HeightOneSpectrum.equivOfRingEquiv oL).symm P
  have hQ : Q.asIdeal = P.asIdeal.comap oL := rfl
  obtain ⟨f, α, h1, h2, h3⟩ := h Q (by rw [hQ, Ideal.mem_comap, map_natCast]; exact hP)
  have hcm : Q.asIdeal.comap (RingOfIntegers.mapRingHom φ) =
      (P.asIdeal.comap (RingOfIntegers.mapRingHom φ')).comap oK := by
    ext x
    rw [hQ]
    simp only [Ideal.mem_comap]
    have : RingOfIntegers.mapRingHom φ' (oK x) = oL (RingOfIntegers.mapRingHom φ x) :=
      RingOfIntegers.ext (hc x)
    rw [this]
  rw [hcm, absNorm_comap, hQ, absNorm_comap] at h1
  rw [hcm] at h2
  refine ⟨f, oK α, h1, ?_, ?_⟩
  · have := congrArg (Ideal.map oK) h2
    rwa [Ideal.map_pow, Ideal.map_comap_of_surjective _ oK.surjective, Ideal.map_span, Set.image_singleton] at this
  · have := map_dvd oK h3
    rwa [map_natCast, map_sub, map_one] at this

theorem weberIn_of_containsRayField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (φ : K →+* L) (ψ : L →+* ℂ), Module.finrank ℚ K = 2 → (∃ a : K, a ^ 2 = -(H.d : K)) → ∀ n : ℕ, 3 ≤ n → GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField φ n → GlobalTheory.FinalJoin.WeberIn H ψ.toRatAlgHom.fieldRange n ∧ H.rt0 ∈ ψ.toRatAlgHom.fieldRange := by
  intro E _ _ _ H K L _ _ _ _ φ ψ h2 ⟨a, ha⟩ n hn hC
  have hdm := H.d_mod
  have hd0 : 0 < H.d := H.d_prime.pos
  let eK : K ≃ₐ[ℚ] (ψ.comp φ).toRatAlgHom.fieldRange := AlgEquiv.ofInjectiveField (ψ.comp φ).toRatAlgHom
  let eL : L ≃ₐ[ℚ] ψ.toRatAlgHom.fieldRange := AlgEquiv.ofInjectiveField ψ.toRatAlgHom
  have heK : ∀ x, ((eK x : (ψ.comp φ).toRatAlgHom.fieldRange) : ℂ) = ψ (φ x) := fun _ => rfl
  have heL : ∀ x, ((eL x : ψ.toRatAlgHom.fieldRange) : ℂ) = ψ x := fun _ => rfl
  have hr0 : H.rt0 ∈ (ψ.comp φ).toRatAlgHom.fieldRange := by
    have h1 : (ψ (φ a)) ^ 2 = H.rt0 ^ 2 := by
      rw [H.sqrt_neg_disc_sq, ← map_pow, ← map_pow, ha]; simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
    · exact ⟨a, h⟩
    · exact ⟨-a, by
        change ψ (φ (-a)) = _
        rw [map_neg, map_neg, h, neg_neg]⟩
  have hle : (ψ.comp φ).toRatAlgHom.fieldRange ≤ ψ.toRatAlgHom.fieldRange := by
    rintro _ ⟨x, rfl⟩
    exact ⟨φ x, rfl⟩
  clear_value eK eL
  generalize (ψ.comp φ).toRatAlgHom.fieldRange = K₀ at eK heK hr0 hle
  generalize ψ.toRatAlgHom.fieldRange = F at eL heL hle ⊢
  have hfK : FiniteDimensional ℚ K₀ := eK.toLinearEquiv.finiteDimensional
  have hfF : FiniteDimensional ℚ F := eL.toLinearEquiv.finiteDimensional
  have hNK : NumberField K₀ := NumberField.mk
  have hNF : NumberField F := NumberField.mk
  replace h2 : Module.finrank ℚ K₀ = 2 := by rw [← eK.toLinearEquiv.finrank_eq, h2]
  have hC' : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (IntermediateField.inclusion hle).toRingHom n :=
    containsRayField_congr φ _ eK.toRingEquiv eL.toRingEquiv
      (fun x => Subtype.ext ((heK x).trans (heL (φ x)).symm)) n hC
  have hr : (⟨H.rt0, hr0⟩ : K₀) ^ 2 = -(H.d : K₀) := Subtype.ext (by simpa using H.sqrt_neg_disc_sq)
  have hD : discr K₀ = -(H.d : ℤ) := discr_eq_neg_of_sq_eq h2 H.d_prime.squarefree (by omega) hr
  have hTC : IsTotallyComplex K₀ := by
    refine ⟨fun v => ?_⟩
    rw [← InfinitePlace.not_isReal_iff_isComplex]
    intro hv
    have h1 : InfinitePlace.embedding_of_isReal hv ⟨H.rt0, hr0⟩ ^ 2 = -(H.d : ℝ) := by
      rw [← map_pow, hr, map_neg, map_natCast]
    have h3 : (0 : ℝ) < H.d := by exact_mod_cast hd0
    nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hv ⟨H.rt0, hr0⟩)]
  obtain ⟨w, hw, hgen⟩ := exists_integer_generator_of_sq_eq_neg h2 H.d_prime.squarefree (by omega) hr
  let j : K₀ →+* ℂ := algebraMap K₀ ℂ
  have hw' : j w = (1 + H.rt0) / 2 := by
    have := congrArg j hw
    rw [map_mul, map_add, map_one, map_ofNat] at this
    change _ = 1 + H.rt0 at this
    linear_combination this / 2
  have hc : ∀ a b : ℤ, j ((a : 𝓞 K₀) + b * w : 𝓞 K₀) = a + b * ((1 + H.rt0) / 2) := fun a b => by
    rw [← hw']
    simp
  refine ⟨fun P hP => ?_, hle hr0⟩
  have hW := GlobalTheory.T.weberInvariantTorsionValues_subset_of_containsRayField K₀ F hle h2 (by omega) P (fun z => ?_) n hn hC'
  · exact ⟨hW (Set.mem_insert _ _), fun s hs => hW (Set.mem_insert_of_mem _
      ⟨_, (hP _).2 ⟨s, rfl⟩, hs, rfl⟩)⟩
  · rw [hP]
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨_, hc s.1 s.2⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨a, b, rfl⟩ := hgen a
      exact ⟨(a, b), hc a b⟩

end GlobalTheory.FieldSize.WeberTransport
