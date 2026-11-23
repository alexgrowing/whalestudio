import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsPrismLocalizationAwayOfGeneratedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismHomMapIdealEqStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isPushout_of_away {A C A' C' : Type} [CommRing A] [CommRing C] [CommRing A'] [CommRing C']
    (h : A →+* C) (k : A →+* A') (k' : C →+* C') (h' : A' →+* C') (e : k'.comp h = h'.comp k) (x : A)
    (H : letI := h.toAlgebra; IsLocalization.Away x C)
    (H' : letI := h'.toAlgebra; IsLocalization.Away (k x) C') :
    CategoryTheory.IsPushout (CommRingCat.ofHom h) (CommRingCat.ofHom k) (CommRingCat.ofHom k')
      (CommRingCat.ofHom h') := by
  letI : Algebra A C := h.toAlgebra
  letI : Algebra A A' := k.toAlgebra
  letI : Algebra C C' := k'.toAlgebra
  letI : Algebra A' C' := h'.toAlgebra
  letI : Algebra A C' := (h'.comp k).toAlgebra
  haveI : IsScalarTower A A' C' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A C C' := IsScalarTower.of_algebraMap_eq fun a => (RingHom.congr_fun e a).symm
  haveI : IsLocalization (Submonoid.powers x) C := H
  haveI : IsLocalization (Algebra.algebraMapSubmonoid A' (Submonoid.powers x)) C' := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    exact H'
  haveI : Algebra.IsPushout A A' C C' :=
    Algebra.isPushout_of_isLocalization (Submonoid.powers x) C A' C'
  exact (CommRingCat.isPushout_iff_isPushout (R := A) (R' := C) (S := A') (S' := C')).2
    (Algebra.IsPushout.symm inferInstance)

theorem IsLoc.isUnit_of_complete {l : ℕ} {R : Type} [CommRing R] {B C : Obj l R} {s : B.A} {h : Hom B C}
    (H : IsLoc s h) : IsUnit (h.f s) := by
  have hu : IsUnit (qmap h 1 (Ideal.Quotient.mk (adI B ^ 1) s)) := by
    letI := (qmap h 1).toAlgebra
    haveI := H.away 1
    exact IsLocalization.Away.algebraMap_isUnit _
  rw [qmap_mk] at hu
  haveI := C.complete
  have hj : adI C ^ 1 ≤ (⊥ : Ideal C.A).jacobson := by
    rw [pow_one]
    exact IsAdicComplete.le_jacobson_bot _
  haveI := isLocalHom_of_le_jacobson_bot _ hj
  exact IsUnit.of_map (Ideal.Quotient.mk _) _ hu

theorem stable_of_isLoc : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C : Obj l R) (s : B.A) (h : Hom B C),
    (∃ t ∈ B.I, ∀ x ∈ B.I, ∃ k : ℕ, s ^ k * x ∈ Ideal.span {t}) → IsLoc s h → Stable h := by
  rintro l _ R _ B C s h ⟨t, ht, hst⟩ H
  refine ⟨fun m => ?_, fun B' k => ?_⟩
  · letI := (qmap h m).toAlgebra
    haveI := H.away m
    exact IsLocalization.flat _ (Submonoid.powers (Ideal.Quotient.mk (adI B ^ m) s))
  ·
    have hgen : GenAway B' (k.f s) (k.f t) := by
      refine ⟨k.f_I t ht, fun x hx => ?_⟩
      rw [← GlobalTheory.T.prism_hom_map_ideal_eq l R B B' k] at hx
      have hx' : x ∈ Ideal.span (k.f '' B.I) := hx
      refine Submodule.span_induction
        (p := fun x _ => ∃ n : ℕ, k.f s ^ n * x ∈ Ideal.span {k.f t}) ?_ ?_ ?_ ?_ hx'
      · rintro _ ⟨y, hy, rfl⟩
        obtain ⟨n, hn⟩ := hst y hy
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
        refine ⟨n, Ideal.mem_span_singleton'.2 ⟨k.f c, ?_⟩⟩
        simpa only [map_mul, map_pow] using congrArg k.f hc
      · exact ⟨0, by simp⟩
      · rintro a b _ _ ⟨n₁, h₁⟩ ⟨n₂, h₂⟩
        refine ⟨n₁ + n₂, ?_⟩
        have hab : k.f s ^ (n₁ + n₂) * (a + b) =
            k.f s ^ n₂ * (k.f s ^ n₁ * a) + k.f s ^ n₁ * (k.f s ^ n₂ * b) := by ring
        rw [hab]
        exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h₁) (Ideal.mul_mem_left _ _ h₂)
      · rintro a b _ ⟨n, hn⟩
        refine ⟨n, ?_⟩
        rw [smul_eq_mul, mul_left_comm]
        exact Ideal.mul_mem_left _ _ hn
    obtain ⟨C', h', hloc', -⟩ := GlobalTheory.T.exists_isPrismLocalizationAway_of_generated l R B' (k.f s) (k.f t) hgen
    obtain ⟨k', hk'⟩ := H.univ C' (h'.comp k)
      (show IsUnit (h'.f (k.f s)) from IsLoc.isUnit_of_complete hloc')
    refine ⟨C', k', h', hk', fun m => ?_⟩
    refine isPushout_of_away (qmap h m) (qmap k m) (qmap k' m) (qmap h' m) ?_
      (Ideal.Quotient.mk _ s) (H.away m) ?_
    · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_)
      simp only [RingHom.comp_apply, qmap_mk]
      exact congrArg (fun g : Hom B C' => Ideal.Quotient.mk (adI C' ^ m) (g.f a)) hk'
    · rw [qmap_mk]
      exact hloc'.away m

end GlobalTheory.BSP
