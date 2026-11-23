import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory

namespace TraceDualFamily

open scoped nonZeroDivisors

variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

lemma conj_conj (c : E ≃ₐ[ℚ] E) (φ₀ : E →+* ℂ)
    (hc : ∀ (φ : E →+* ℂ) (x : E), φ (c x) = starRingEnd ℂ (φ x)) (x : E) : c (c x) = x := by
  apply φ₀.injective
  rw [hc, hc, Complex.conj_conj]

lemma mem_range_iff (x : K) : x ∈ (algebraMap (𝓞 K) K).range ↔ IsIntegral ℤ x :=
  ⟨by rintro ⟨y, rfl⟩; exact RingOfIntegers.isIntegral_coe y, fun h => ⟨⟨x, h⟩, rfl⟩⟩

lemma isIntegral_trace_conj (c : E ≃ₐ[ℚ] E) (φ₀ : E →+* ℂ)
    (hc : ∀ (φ : E →+* ℂ) (x : E), φ (c x) = starRingEnd ℂ (φ x)) (z : E)
    (hz : IsIntegral ℤ (Algebra.trace K E z)) : IsIntegral ℤ (Algebra.trace K E (c z)) := by
  letI : Algebra K ℂ := (φ₀.comp (algebraMap K E)).toAlgebra
  have h1 : algebraMap K ℂ (Algebra.trace K E (c z)) =
      starRingEnd ℂ (algebraMap K ℂ (Algebra.trace K E z)) := by
    rw [trace_eq_sum_embeddings ℂ, trace_eq_sum_embeddings ℂ, map_sum]
    exact Finset.sum_congr rfl fun σ _ => hc (σ : E →+* ℂ) z
  have h2 : IsIntegral ℤ (algebraMap K ℂ (Algebra.trace K E (c z))) := by
    rw [h1]
    exact (hz.map (algebraMap K ℂ).toIntAlgHom).map (starRingEnd ℂ).toIntAlgHom
  exact (isIntegral_algHom_iff (algebraMap K ℂ).toIntAlgHom (algebraMap K ℂ).injective).mp h2

lemma isLocalizedModule_subtype (Λ : Submodule (𝓞 K) E)
    (h : Submodule.span K (Λ : Set E) = ⊤) : IsLocalizedModule (𝓞 K)⁰ Λ.subtype where
  map_units s := by
    have := isLocalizedModule_id (𝓞 K)⁰ E K
    exact IsLocalizedModule.map_units (S := (𝓞 K)⁰) (LinearMap.id : E →ₗ[𝓞 K] _) s
  surj y := by
    have hy : y ∈ Submodule.span K (Λ : Set E) := h ▸ Submodule.mem_top
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (𝓞 K)⁰ K _ y hy
    rw [Submodule.span_eq] at ht
    exact ⟨(⟨_, ht⟩, t), rfl⟩
  exists_of_eq h := ⟨1, by simpa using h⟩

theorem exists_family (c : E ≃ₐ[ℚ] E) (φ₀ : E →+* ℂ)
    (hc : ∀ (φ : E →+* ℂ) (x : E), φ (c x) = starRingEnd ℂ (φ x))
    (I : FractionalIdeal (𝓞 E)⁰ E)
    (hI : ∀ x : E, x ∈ I ↔ ∀ y ∈ I, Algebra.trace K E (x * c y) ∈ (algebraMap (𝓞 K) K).range) :
    ∃ (r : ℕ) (a a' : Fin r → E), (∀ k, a k ∈ I) ∧ (∀ k, a' k ∈ I) ∧
      ∀ t : E, t = ∑ k, (Algebra.trace K E (t * c (a' k))) • a k := by
  have hI0 : I ≠ 0 := by
    rintro rfl
    have := (hI 1).mpr (by
      intro y hy
      rw [FractionalIdeal.mem_zero_iff] at hy
      subst hy
      simp)
    rw [FractionalIdeal.mem_zero_iff] at this
    exact one_ne_zero this
  let Λ : Submodule (𝓞 K) E := (I : Submodule (𝓞 E) E).restrictScalars (𝓞 K)
  have hsp : Submodule.span K (Λ : Set E) = ⊤ := by
    obtain ⟨x, hx, hx0⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger hI0
    rw [eq_top_iff]
    intro t _
    have hx' : algebraMap (𝓞 E) E x ≠ 0 := by simpa using hx
    have halg : IsAlgebraic ℤ (t / algebraMap (𝓞 E) E x) :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic _)
    obtain ⟨n, hn0, hn⟩ := halg.exists_integral_multiple
    have hmem : (n : E) * t ∈ Λ := by
      have := (I : Submodule (𝓞 E) E).smul_mem (⟨_, hn⟩ : 𝓞 E) hx0
      convert this using 1
      change _ ↔ (n • (t / algebraMap (𝓞 E) E x)) * algebraMap (𝓞 E) E x ∈ _
      rw [zsmul_eq_mul, mul_assoc, div_mul_cancel₀ _ hx']
      rfl
    have hnK : (n : K) ≠ 0 := by exact_mod_cast hn0
    have : t = (n : K)⁻¹ • ((n : E) * t) := by
      have hnE : (n : E) ≠ 0 := by exact_mod_cast hn0
      rw [Algebra.smul_def, map_inv₀, map_intCast, inv_mul_cancel_left₀ hnE]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  have : Module.Finite (𝓞 K) Λ := Module.Finite.iff_fg.mpr
    (Submodule.FG.restrictScalars (FractionalIdeal.fg_of_isNoetherianRing le_rfl I))
  have : Module.FinitePresentation (𝓞 K) Λ := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) Λ := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, f, g, -, -, hfg'⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 K) Λ
  have := isLocalizedModule_subtype Λ hsp
  have hext : ∀ i : Fin m, ∃ w : E, ∀ y : Λ, Algebra.trace K E ((y : E) * c w) = (g y i : K) := by
    intro i
    let φ : Λ →ₗ[𝓞 K] K := Algebra.linearMap (𝓞 K) K ∘ₗ LinearMap.proj i ∘ₗ g
    let ψ : E →ₗ[𝓞 K] K := IsLocalizedModule.lift (𝓞 K)⁰ Λ.subtype φ
      (IsLocalizedModule.map_units (S := (𝓞 K)⁰) (Algebra.linearMap (𝓞 K) K))
    obtain ⟨u, hu⟩ := ((Algebra.traceForm K E).toDual (traceForm_nondegenerate K E)).surjective
      (ψ.extendScalarsOfIsLocalization (𝓞 K)⁰ K)
    refine ⟨c.symm u, fun y => ?_⟩
    have h1 := LinearMap.congr_fun hu (y : E)
    rw [LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply] at h1
    rw [AlgEquiv.apply_symm_apply, mul_comm, h1]
    exact IsLocalizedModule.lift_apply (𝓞 K)⁰ Λ.subtype φ
      (IsLocalizedModule.map_units (S := (𝓞 K)⁰) (Algebra.linearMap (𝓞 K) K)) y
  choose w hw using hext
  refine ⟨m, fun i => (f (Pi.single i 1) : E), w, fun i => Subtype.prop (f (Pi.single i 1)),
    fun i => ?_, ?_⟩
  · refine (hI _).mpr fun y hy => (mem_range_iff _).mpr ?_
    have e : w i * c y = c (y * c (w i)) := by rw [map_mul, conj_conj c φ₀ hc, mul_comm]
    rw [e]
    refine isIntegral_trace_conj c φ₀ hc _ ?_
    rw [hw i ⟨y, hy⟩]
    exact RingOfIntegers.isIntegral_coe _
  · intro u
    have hu : u ∈ Submodule.span K (Λ : Set E) := hsp ▸ Submodule.mem_top
    induction hu using Submodule.span_induction with
    | mem y hy =>
      have h1 : f (g ⟨y, hy⟩) = ⟨y, hy⟩ := LinearMap.congr_fun hfg' _
      have h2 : g ⟨y, hy⟩ = ∑ i, g ⟨y, hy⟩ i • (Pi.single i 1 : Fin m → 𝓞 K) := by
        ext j; simp [Pi.single_apply]
      rw [h2, map_sum] at h1
      have h3 := congrArg Subtype.val h1
      simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul] at h3
      refine h3.symm.trans (Finset.sum_congr rfl fun i _ => ?_)
      rw [hw i ⟨y, hy⟩]
      exact (algebraMap_smul K _ _).symm
    | zero => simp
    | add x y _ _ hx hy =>
      conv_lhs => rw [hx, hy]
      simp [add_mul, Finset.sum_add_distrib, add_smul]
    | smul a x _ hx =>
      conv_lhs => rw [hx]
      simp [Finset.smul_sum, mul_smul]

end TraceDualFamily

theorem exists_trace_dual_family_halfDifferent : ∀ (D : D7), ∃ (r : ℕ) (a a' : Fin r → D.host.E), (∀ k, a k ∈ D.host.AA0) ∧ (∀ k, a' k ∈ D.host.AA0) ∧ ∀ t : D.host.E, t = ∑ k, (Algebra.trace D.host.K D.host.E (t * D.host.conj (a' k))) • a k :=
  fun D => TraceDualFamily.exists_family D.host.conj D.host.φ₀
    (fun φ x => D.host.conjE_apply φ x) D.host.AA0
    (factMMUnimodular D.R D.host)

end GlobalTheory
