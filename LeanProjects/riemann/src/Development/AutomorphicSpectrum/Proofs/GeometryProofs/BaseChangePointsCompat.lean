import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem genericBaseChange_ringHom_eq {R : Type} [CommRing R] [IsDomain R]
    {R' : Type} [CommRing R'] [IsDomain R'] [Algebra R R'] {B : Type} [CommRing B]
    (i : R →+* B) (j : B →+* FractionRing R) (j' : B →+* FractionRing R')
    (κ : FractionRing R →+* FractionRing R')
    (hκ : κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R'))
    (hj : Function.Injective j) (hji : j.comp i = algebraMap R _)
    (hj'i : j'.comp i = (algebraMap R' _).comp (algebraMap R R')) :
    j' = κ.comp j := by
  ext b
  obtain ⟨r, s, hs, hrs⟩ := IsFractionRing.div_surjective (A := R) (j b)
  have hs0 : algebraMap R (FractionRing R) s ≠ 0 := by
    simpa using IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := FractionRing R) hs
  have e1 : algebraMap R (FractionRing R) s * j b = algebraMap R (FractionRing R) r := by
    rw [← hrs]; field_simp
  have hjs : ∀ x : R, j (i x) = algebraMap R (FractionRing R) x := fun x =>
    RingHom.congr_fun hji x
  have e2 : i s * b = i r := by
    apply hj
    rw [map_mul, hjs, hjs, e1]
  have hj's : ∀ x : R, j' (i x) = κ (algebraMap R (FractionRing R) x) := fun x =>
    (RingHom.congr_fun hj'i x).trans (RingHom.congr_fun hκ x).symm
  have e3 : κ (algebraMap R (FractionRing R) s) * j' b = κ (algebraMap R (FractionRing R) r) := by
    rw [← hj's, ← hj's, ← map_mul, e2]
  have e4 : κ (algebraMap R (FractionRing R) s) * κ (j b) = κ (algebraMap R (FractionRing R) r) := by
    rw [← map_mul, e1]
  have hκs : κ (algebraMap R (FractionRing R) s) ≠ 0 := by
    simpa using hs0
  exact mul_left_cancel₀ hκs (e3.trans e4.symm)

theorem genericPoint_baseChange :
    ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → ∀ κ : FractionRing R →+* FractionRing R', κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R') → ∀ t, (Γ'.pt t).left ≫ F = Spec.map (CommRingCat.ofHom κ) ≫ (Γ.pt t).left := by
  intro R _ _ T _ _ Γ R' _ _ _ Γ' F hF κ hκ t
  obtain ⟨B, _, i, j, j', σ, hj, hji, hj'i, -, hσ, hσ'⟩ := hF.pts
  have hjj : j' = κ.comp j := genericBaseChange_ringHom_eq i j j' κ hκ hj hji hj'i
  rw [← hσ' t, ← hσ t, hjj, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

end GlobalTheory.CompanionTheory.Ar.BT
