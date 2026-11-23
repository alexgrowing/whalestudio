import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.SpacesExOf

open scoped nonZeroDivisors Matrix Pointwise
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.Gal.TP.Skew

namespace UpperTheory.Gal.TP.Skew

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end

end UpperTheory.Gal.TP.Skew

private theorem count_le_count_galois_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (g : Gal(E/F)) (P : HeightOneSpectrum (𝓞 E)) (J : Ideal (𝓞 E)) (hJ : J ≠ 0) :
    FractionalIdeal.count E P (J : FractionalIdeal (𝓞 E)⁰ E) ≤
      FractionalIdeal.count E (g • P) ((g • J : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) := by
  classical
  have hgJ : g • J ≠ 0 := fun h => hJ ((smul_eq_zero_iff_eq g).mp h)
  rw [FractionalIdeal.count_coe E P hJ, FractionalIdeal.count_coe E (g • P) hgJ, Nat.cast_le,
    ← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hgJ)
      (g • P).associates_irreducible]
  have h1 := (Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ)
    P.associates_irreducible).mpr le_rfl
  rw [← Associates.mk_pow, Associates.mk_le_mk_iff_dvd] at h1 ⊢
  obtain ⟨c, hc⟩ := h1
  refine ⟨g • c, ?_⟩
  change g • J = (g • P.asIdeal) ^ _ * g • c
  conv_lhs => rw [hc]
  rw [smul_mul', smul_pow']

private theorem count_galois_smul_eq_count {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (g : Gal(E/F)) (P : HeightOneSpectrum (𝓞 E)) (J : Ideal (𝓞 E)) (hJ : J ≠ 0) :
    FractionalIdeal.count E (g • P) ((g • J : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) =
      FractionalIdeal.count E P (J : FractionalIdeal (𝓞 E)⁰ E) := by
  refine le_antisymm ?_ (count_le_count_galois_smul g P J hJ)
  have h := count_le_count_galois_smul g⁻¹ (g • P) (g • J) (fun h => hJ ((smul_eq_zero_iff_eq g).mp h))
  rwa [inv_smul_smul, inv_smul_smul] at h

private theorem count_smul_eq_of_mem_iff_inv_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (g : Gal(E/F)) (w : HeightOneSpectrum (𝓞 E))
    (I I' : FractionalIdeal (𝓞 E)⁰ E) (hI : I ≠ 0) (h : ∀ x : E, x ∈ I' ↔ (g⁻¹ : Gal(E/F)) x ∈ I) :
    FractionalIdeal.count E (g • w) I' = FractionalIdeal.count E w I := by
  obtain ⟨b, J, hb, hbJ⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  have hJ : J ≠ 0 := FractionalIdeal.ideal_factor_ne_zero hI hbJ
  have hb' : Ideal.span {b} ≠ 0 := FractionalIdeal.constant_factor_ne_zero hI hbJ
  have hspan : g • Ideal.span {b} = Ideal.span {g • b} := by
    rw [Ideal.pointwise_smul_def, Ideal.map_span, Set.image_singleton]
    rfl
  have hinv : ∀ y : E, (g⁻¹ : Gal(E/F)) (g y) = y := fun y => by simp
  have hI' : I' = FractionalIdeal.spanSingleton (𝓞 E)⁰ (algebraMap (𝓞 E) E (g • b))⁻¹ *
      ((g • J : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) := by
    ext x
    rw [h, hbJ, FractionalIdeal.mem_singleton_mul, FractionalIdeal.mem_singleton_mul]
    simp only [FractionalIdeal.mem_coeIdeal]
    constructor
    · rintro ⟨_, ⟨j, hj, rfl⟩, hx⟩
      have hgj : g • j ∈ g • J := by
        rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul]
        exact hj
      refine ⟨_, ⟨g • j, hgj, rfl⟩, ?_⟩
      have hx' : x = g ((g⁻¹ : Gal(E/F)) x) := by simp
      rw [hx', hx, map_mul, map_inv₀]
      rfl
    · rintro ⟨_, ⟨j, hj, rfl⟩, hx⟩
      refine ⟨_, ⟨g⁻¹ • j, Ideal.mem_pointwise_smul_iff_inv_smul_mem.mp hj, rfl⟩, ?_⟩
      rw [hx, map_mul, map_inv₀]
      exact congrArg₂ (· * ·) (congrArg Inv.inv (hinv (algebraMap (𝓞 E) E b))) rfl
  have hgJ : g • J ≠ 0 := fun h => hJ ((smul_eq_zero_iff_eq g).mp h)
  have hgb : g • Ideal.span {b} ≠ 0 := fun h => hb' ((smul_eq_zero_iff_eq g).mp h)
  rw [hI', hbJ, ← FractionalIdeal.spanSingleton_inv, ← FractionalIdeal.spanSingleton_inv,
    ← FractionalIdeal.coeIdeal_span_singleton, ← FractionalIdeal.coeIdeal_span_singleton, ← hspan,
    FractionalIdeal.count_mul E (g • w) (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.mpr hgb))
      (FractionalIdeal.coeIdeal_ne_zero.mpr hgJ),
    FractionalIdeal.count_mul E w (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.mpr hb'))
      (FractionalIdeal.coeIdeal_ne_zero.mpr hJ),
    FractionalIdeal.count_inv, FractionalIdeal.count_inv, count_galois_smul_eq_count g w _ hb', count_galois_smul_eq_count g w J hJ]

private theorem galois_apply_mem_dual_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (h : Gal(E/F)) (y : E)
    (hy : y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)) :
    h y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
  have hinv : ∀ y : E, (h⁻¹ : Gal(E/F)) (h y) = y := fun y => by simp
  have h1 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    rw [← FractionalIdeal.coeIdeal_top]
    exact FractionalIdeal.coeIdeal_ne_zero.mpr top_ne_bot
  rw [FractionalIdeal.mem_dual h1] at hy ⊢
  intro a ha
  obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
  have hz := hy (algebraMap (𝓞 E) E (h⁻¹ • z)) ((FractionalIdeal.mem_one_iff _).mpr ⟨_, rfl⟩)
  rw [Algebra.traceForm_apply] at hz ⊢
  have e : Algebra.trace ℚ E (h y * algebraMap (𝓞 E) E z) =
      Algebra.trace ℚ E (y * algebraMap (𝓞 E) E (h⁻¹ • z)) := by
    rw [← Algebra.trace_eq_of_algEquiv ((h⁻¹ : Gal(E/F)).restrictScalars ℚ)
      (h y * algebraMap (𝓞 E) E z)]
    change Algebra.trace ℚ E ((h⁻¹ : Gal(E/F)) (h y * algebraMap (𝓞 E) E z)) = _
    rw [map_mul, hinv]
    rfl
  rw [e]
  exact hz

theorem UpperTheory.Gal.TP.Skew.ordAut :
    UpperTheory.Gal.TP.Skew.OrdAut := by
  intro F E _ _ _ _ _ g w
  have hinv : ∀ y : E, (g⁻¹ : Gal(E/F)) (g y) = y := fun y => by simp
  have hinv2 : ∀ y : E, g ((g⁻¹ : Gal(E/F)) y) = y := fun y => by simp
  refine ⟨fun x => ?_, ?_⟩
  · change FractionalIdeal.count E (g • w) (FractionalIdeal.spanSingleton (𝓞 E)⁰ (g x)) =
      FractionalIdeal.count E w (FractionalIdeal.spanSingleton (𝓞 E)⁰ x)
    by_cases hx : x = 0
    · subst hx
      simp [FractionalIdeal.count_zero]
    · apply count_smul_eq_of_mem_iff_inv_mem g w
      · exact FractionalIdeal.spanSingleton_eq_zero_iff.not.mpr hx
      · intro y
        simp only [FractionalIdeal.mem_spanSingleton, Algebra.smul_def]
        constructor
        · rintro ⟨z, rfl⟩
          refine ⟨g⁻¹ • z, ?_⟩
          rw [map_mul, hinv]
          rfl
        · rintro ⟨z, hz⟩
          refine ⟨g • z, ?_⟩
          rw [← hinv2 y, ← hz, map_mul]
          rfl
  · apply count_smul_eq_of_mem_iff_inv_mem g w
    · refine FractionalIdeal.dual_ne_zero ℤ ℚ ?_
      rw [← FractionalIdeal.coeIdeal_top]
      exact FractionalIdeal.coeIdeal_ne_zero.mpr top_ne_bot
    · intro y
      constructor
      · exact galois_apply_mem_dual_one g⁻¹ y
      · intro hy
        have := galois_apply_mem_dual_one g _ hy
        rwa [hinv2] at this
