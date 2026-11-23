import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyCompletedLocalizationPrismStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismHomMapIdealEqStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

variable {l : ℕ} {R : Type} [CommRing R]

theorem adI_pow_eq_map_of_map_I {B C : Obj l R} (h : Hom B C) (hI : B.I.map h.f = C.I) (m : ℕ) :
    adI C ^ m = (adI B ^ m).map h.f := by
  rw [Ideal.map_pow]
  congr 1
  simp only [adI, Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast, hI]

theorem isLoc_of_locP (hrig : ∀ (B B' : Obj l R) (f : Hom B B'), B.I.map f.f = B'.I)
    {B : Obj l R} {s d : B.A} (L : LocP B s d) : IsLoc s L.inl := by
  have hJ : ∀ m, adI L.Q ^ m = (adI B ^ m).map L.inl.f :=
    adI_pow_eq_map_of_map_I L.inl (hrig _ _ _)
  refine ⟨fun m => ?_, fun Q a ha => ?_⟩
  · letI := (qmap L.inl m).toAlgebra
    have hmap : ∀ b : B.A, algebraMap (B.A ⧸ adI B ^ m) (L.Q.A ⧸ adI L.Q ^ m) (Ideal.Quotient.mk _ b) =
        Ideal.Quotient.mk _ (L.inl.f b) := fun b => rfl
    refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
    · rintro ⟨y, k, rfl⟩
      change IsUnit (algebraMap (B.A ⧸ adI B ^ m) (L.Q.A ⧸ adI L.Q ^ m) (Ideal.Quotient.mk _ s ^ k))
      rw [map_pow, hmap]
      exact (L.unit.map _).pow k
    · intro z
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨k, b, hkb⟩ := L.surj c m
      refine ⟨⟨Ideal.Quotient.mk _ b, ⟨Ideal.Quotient.mk _ s ^ k, k, rfl⟩⟩, ?_⟩
      change Ideal.Quotient.mk _ c * algebraMap (B.A ⧸ adI B ^ m) (L.Q.A ⧸ adI L.Q ^ m)
        (Ideal.Quotient.mk _ s ^ k) = algebraMap (B.A ⧸ adI B ^ m) (L.Q.A ⧸ adI L.Q ^ m) (Ideal.Quotient.mk _ b)
      rw [map_pow, hmap, hmap, ← map_pow, ← map_mul, Ideal.Quotient.eq, hJ, mul_comm]
      exact hkb
    · intro x y hxy
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [hmap, hmap, Ideal.Quotient.eq, hJ, ← map_sub] at hxy
      obtain ⟨k, hk⟩ := L.ker (a - b) m hxy
      refine ⟨⟨Ideal.Quotient.mk _ s ^ k, k, rfl⟩, ?_⟩
      change Ideal.Quotient.mk _ s ^ k * Ideal.Quotient.mk _ a = Ideal.Quotient.mk _ s ^ k * Ideal.Quotient.mk _ b
      rw [← map_pow, ← map_mul, ← map_mul, Ideal.Quotient.eq, ← mul_sub]
      exact hk
  · obtain ⟨c, hc, -⟩ := L.univ Q a ha
    exact ⟨c, hc⟩

theorem exists_isLoc : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B : Obj l R) (s d : B.A), GenAway B s d →
    ∃ (C : Obj l R) (h : Hom B C), IsLoc s h ∧ C.I = Ideal.span {h.f d} := by
  intro l _ R _ B s d hg
  obtain ⟨L⟩ := GlobalTheory.T.nonempty_completedLocalizationPrism l R B s d hg
  exact ⟨L.Q, L.inl, isLoc_of_locP (GlobalTheory.T.prism_hom_map_ideal_eq l R) L, L.I_eq⟩

end GlobalTheory.BSP
