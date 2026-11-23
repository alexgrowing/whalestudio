import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC

theorem chains_spMap_comp (R : Type) [CommRing R] {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : A →+* B)
    (h : B →+* C) : (chains R).map (spMap h) ≫ (chains R).map (spMap g) = (chains R).map (spMap (h.comp g)) := by
  rw [← Functor.map_comp]
  congr 1
  simp only [spMap, ← Functor.map_comp, ← Spec.map_comp]
  rfl

theorem awayMap_comp_algebraMap {A B : Type} [CommRing A] [CommRing B] (g : A →+* B) (f : A) :
    (Localization.awayMap g f).comp (algebraMap A (Localization.Away f)) = (algebraMap B (Localization.Away (g f))).comp g :=
  IsLocalization.map_comp _

theorem excision_square_comm (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A) :
    (chains R).map (spMap (algebraMap A' (Localization.Away (algebraMap A A' f)))) ≫ (chains R).map (spMap (algebraMap A A')) =
      (chains R).map (spMap (Localization.awayMap (algebraMap A A') f)) ≫
        (chains R).map (spMap (algebraMap A (Localization.Away f))) := by
  rw [chains_spMap_comp, chains_spMap_comp, awayMap_comp_algebraMap]

def excisionConeMap (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A) :
    mappingCone ((chains R).map (spMap (algebraMap A' (Localization.Away (algebraMap A A' f))))) ⟶
      mappingCone ((chains R).map (spMap (algebraMap A (Localization.Away f)))) :=
  mappingCone.map _ _ _ _ (excision_square_comm R A A' f)

end GlobalTheory.EtC
