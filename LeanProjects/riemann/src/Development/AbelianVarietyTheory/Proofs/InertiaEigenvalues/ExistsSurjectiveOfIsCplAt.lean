import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ProjectionSurjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionUniqueUpToIsoStatement
open IsLocalRing GlobalTheory.Pat

namespace GlobalTheory.Pat

theorem flat_quotientMap_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : φ.Flat)
    (I : Ideal R) : (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map).Flat := by
  algebraize [φ]
  have h1 : (algebraMap (R ⧸ I) (TensorProduct R (R ⧸ I) S)).Flat :=
    RingHom.flat_algebraMap_iff.2 inferInstance
  let e : TensorProduct R (R ⧸ I) S ≃+* S ⧸ I.map φ :=
    (Algebra.TensorProduct.comm R (R ⧸ I) S).toRingEquiv.trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm.toRingEquiv
  have h2 : (e : TensorProduct R (R ⧸ I) S →+* S ⧸ I.map φ).Flat := RingHom.Flat.of_bijective e.bijective
  have h3 := h1.comp h2
  convert h3 using 1
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
  have : (Ideal.Quotient.mk I r) ⊗ₜ[R] (1 : S) = (1 : R ⧸ I) ⊗ₜ[R] (φ r) := by
    have := TensorProduct.smul_tmul (R := R) r (1 : R ⧸ I) (1 : S)
    simp only [Algebra.smul_def, mul_one] at this
    exact this
  simp only [RingHom.comp_apply, Ideal.quotientMap_mk, Algebra.TensorProduct.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply, RingHom.coe_coe]
  rw [this]
  apply (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).injective
  simp [e]
  exact Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk S I (φ r)

theorem exists_surjective_of_isCplAt : ∀ (R R' S S' : Type) [CommRing R] [IsNoetherianRing R] [CommRing R'] [CommRing S] [IsLocalRing S] [CommRing S'] [IsLocalRing S'] (π : R →+* R') (q' : Ideal R') [q'.IsPrime] (φ : R →+* S) (φ' : R' →+* S'), Function.Surjective π → IsCplAt (q'.comap π) φ → IsCplAt q' φ' → ∃ θ : S →+* S', IsLocalHom θ ∧ θ.comp φ = φ'.comp π ∧ Function.Surjective θ ∧ RingHom.ker θ = (RingHom.ker π).map φ := by
  intro R R' S S' _ _ _ _ _ _ _ π q' _ φ φ' hπ h h'
  set J : Ideal S := (RingHom.ker π).map φ with hJ
  have hJm : J ≤ maximalIdeal S := by
    rw [h.max_eq]
    exact Ideal.map_mono (Ideal.ker_le_comap π)
  have hJt : J ≠ ⊤ := fun ht => (maximalIdeal.isMaximal S).ne_top (top_le_iff.1 (ht ▸ hJm))
  haveI : Nontrivial (S ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJt
  haveI : IsLocalRing (S ⧸ J) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  haveI := h.noeth
  haveI := h.complete
  let ε : R' ≃+* R ⧸ RingHom.ker π := (RingHom.quotientKerEquivOfSurjective hπ).symm
  let ψ : R' →+* S ⧸ J :=
    (Ideal.quotientMap J φ Ideal.le_comap_map).comp (ε : R' →+* R ⧸ RingHom.ker π)
  have hψ : ∀ r, ψ (π r) = Ideal.Quotient.mk J (φ r) := by
    intro r
    have : ε (π r) = Ideal.Quotient.mk _ r := by
      apply ε.symm.injective
      simp [ε]
    simp [ψ, this]
  have hψ' : ψ.comp π = (Ideal.Quotient.mk J).comp φ := RingHom.ext hψ
  have hm : maximalIdeal (S ⧸ J) = (maximalIdeal S).map (Ideal.Quotient.mk J) :=
    (IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective).symm
  have hmc : (maximalIdeal (S ⧸ J)).comap (Ideal.Quotient.mk J) = maximalIdeal S := by
    rw [hm, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.2 hJm]
  have hc : IsCplAt q' ψ :=
    { noeth := inferInstance
      complete := by
        have := GlobalTheory.isAdicComplete_map_of_finite (maximalIdeal S) (S ⧸ J)
        rwa [show algebraMap S (S ⧸ J) = Ideal.Quotient.mk J from rfl, ← hm] at this
      flat := (RingHom.Flat.of_bijective ε.bijective).comp (flat_quotientMap_map φ h.flat _)
      max_eq := by
        rw [hm, h.max_eq, Ideal.map_map, ← hψ', ← Ideal.map_map, Ideal.map_comap_of_surjective π hπ]
      comap_eq := by
        ext x
        obtain ⟨r, rfl⟩ := hπ x
        rw [Ideal.mem_comap, hψ, ← Ideal.mem_comap, hmc, ← Ideal.mem_comap, h.comap_eq, Ideal.mem_comap]
      res := by
        intro s
        obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
        obtain ⟨a, b, hb, hab⟩ := h.res s
        refine ⟨π a, π b, hb, ?_⟩
        rw [hψ, hψ, ← map_mul, ← map_sub, ← Ideal.mem_comap, hmc]
        exact hab }
  obtain ⟨e, he⟩ := GlobalTheory.T.completion_unique_up_to_iso R' (S ⧸ J) S' q' ψ φ' hc h'
  have hs : Function.Surjective ((e : S ⧸ J →+* S').comp (Ideal.Quotient.mk J)) :=
    e.surjective.comp Ideal.Quotient.mk_surjective
  refine ⟨(e : S ⧸ J →+* S').comp (Ideal.Quotient.mk J), IsLocalHom.of_surjective _ hs, ?_, hs, ?_⟩
  · rw [RingHom.comp_assoc, ← hψ', ← RingHom.comp_assoc, he]
  · ext s
    simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

end GlobalTheory.Pat
