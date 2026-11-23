import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BcrisEqAcrisLocalizationPeriodTStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisToBdRPlusInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineTIsUnitBcrisAndUniformizerBdRPlus

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.AwayT

theorem away_of_injective {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (t : R)
    (hu : IsUnit (algebraMap R S t))
    (hs : ∀ b : S, ∃ (r : ℕ) (x : R), b * algebraMap R S t ^ r = algebraMap R S x)
    (hi : Function.Injective (algebraMap R S)) : IsLocalization.Away t S :=
  IsLocalization.Away.mk t hu hs fun _ _ h => ⟨0, by rw [hi h]⟩

theorem lift_injective {R P S : Type} [CommRing R] [CommRing P] [CommRing S] [Algebra R P] (x : R)
    [IsLocalization.Away x P] (f : R →+* S) (g : P →+* S) (hg : ∀ a, g (algebraMap R P a) = f a)
    (hf : Function.Injective f) : Function.Injective g := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj x z
  have h1 : f a = 0 := by rw [← hg, ← ha, map_mul, hz, zero_mul]
  have h2 : a = 0 := hf (h1.trans (map_zero f).symm)
  rw [h2, map_zero] at ha
  exact ((IsLocalization.Away.algebraMap_isUnit (S := P) x).pow n).mul_left_eq_zero.1 ha

variable {l : ℕ} [Fact l.Prime]

theorem plusInj (C : Core l) : C.PlusInj :=
  lift_injective ((l : ℕ) : Per.Acris l) C.j C.jP C.jP_alg (crisP_injective l C.j C.j_cris)

theorem plusToB_injective (C : Core l) : Function.Injective (plusToB l) := fun x y h =>
  plusInj C ((BdRField.bdR_isField l).2.1 (by rw [← C.ι_plusToB, ← C.ι_plusToB, h]))

theorem acris_injective (C : Core l) : Function.Injective (algebraMap (Per.Acris l) (Per.Bcris l)) :=
  fun x y h => crisP_injective l C.j C.j_cris
    ((BdRField.bdR_isField l).2.1 (by rw [← C.ι_j, ← C.ι_j, h]))

theorem awayT (C : Core l) : C.AwayT :=
  away_of_injective C.t (core_t_unit_fil l C).1 (GlobalTheory.T.bcris_eq_acris_localization_periodT l C) (acris_injective C)

theorem plusAwayT (C : Core l) : C.PlusAwayT := by
  letI := (plusToB l).toAlgebra
  have e : ∀ x : Per.Acris l, algebraMap (BcrisP l) (Per.Bcris l) (algebraMap _ _ x) =
      algebraMap (Per.Acris l) (Per.Bcris l) x := plusToB_alg
  refine away_of_injective _ ?_ (fun b => ?_) (plusToB_injective C)
  · rw [e]
    exact (core_t_unit_fil l C).1
  · obtain ⟨r, x, h⟩ := GlobalTheory.T.bcris_eq_acris_localization_periodT l C b
    exact ⟨r, algebraMap _ _ x, by rw [e, e]; exact h⟩

theorem away_and_inj (l : ℕ) [Fact l.Prime] (C : Core l) : C.AwayT ∧ C.PlusAwayT ∧ C.PlusInj :=
  ⟨awayT C, plusAwayT C, plusInj C⟩

end GlobalTheory.MemLoc.AwayT
