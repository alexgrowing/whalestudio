import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XMemOne

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover
open MvPolynomial HomogeneousLocalization

namespace GlobalTheory.PD.XCover

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Overlap

variable {d : ℕ}

def awayRatio (i j : Fin (d + 1)) : Away (homogeneousSubmodule (Fin (d + 1)) ℂ) (X i) :=
  Away.mk (homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d i) 1 (X j) (by simpa using X_mem_one d j)

theorem ratioSec_eq (i j : Fin (d + 1)) :
    ratioSec d i j = Proj.awayToSection (homogeneousSubmodule (Fin (d + 1)) ℂ) (X i) (awayRatio i j) := rfl

theorem germ_awayToSection_mul (a b : Fin (d + 1)) {x : MvPolynomial (Fin (d + 1)) ℂ} (hx : x = X a * X b)
    (y : PSpace ℂ d) (hya : y ∈ chart d a)
    (hy : y ∈ Proj.basicOpen (homogeneousSubmodule (Fin (d + 1)) ℂ) x)
    (s : Away (homogeneousSubmodule (Fin (d + 1)) ℂ) (X a)) :
    (PSpace ℂ d).presheaf.germ (chart d a) y hya
        (Proj.awayToSection (homogeneousSubmodule (Fin (d + 1)) ℂ) (X a) s) =
      (PSpace ℂ d).presheaf.germ _ y hy (Proj.awayToSection (homogeneousSubmodule (Fin (d + 1)) ℂ) x
        (HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d b) hx s)) := by
  have e := ConcreteCategory.congr_hom (Proj.awayMap_awayToSection (homogeneousSubmodule (Fin (d + 1)) ℂ)
    (X_mem_one d b) hx) s
  simp only [ConcreteCategory.comp_apply] at e
  have e' : Proj.awayToSection (homogeneousSubmodule (Fin (d + 1)) ℂ) x
      (HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d b) hx s) =
      (PSpace ℂ d).presheaf.map (homOfLE (Proj.basicOpen_mono _ _ _ ⟨_, hx⟩)).op
        (Proj.awayToSection (homogeneousSubmodule (Fin (d + 1)) ℂ) (X a) s) := e
  rw [e', TopCat.Presheaf.germ_res_apply]

theorem awayRatio_mul_awayRatio (a i : Fin (d + 1)) :
    HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d i)
        (rfl : X a * X i = X a * X i) (awayRatio a i) *
      HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d a)
        (mul_comm (X a) (X i)) (awayRatio i a) = 1 := by
  apply val_injective
  rw [HomogeneousLocalization.val_mul, awayRatio, awayRatio, Away.mk, Away.mk, val_awayMap_mk, val_awayMap_mk,
    HomogeneousLocalization.val_one, Localization.mk_mul]
  rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp
  ring

theorem awayRatio_change (a i j : Fin (d + 1)) :
    HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d a)
        (mul_comm (X a) (X i)) (awayRatio i j) =
      HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d i)
          (rfl : X a * X i = X a * X i) (awayRatio a j) *
        HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d a)
          (mul_comm (X a) (X i)) (awayRatio i a) := by
  apply val_injective
  rw [HomogeneousLocalization.val_mul, awayRatio, awayRatio, awayRatio, Away.mk, Away.mk, Away.mk, val_awayMap_mk,
    val_awayMap_mk, val_awayMap_mk, Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp
  ring

theorem rat_eq_germ {Z : Scheme.{0}} [IsIntegral Z] (φ : Z ⟶ PSpace ℂ d) (k l : Fin (d + 1))
    (hk : genericPoint Z ∈ φ ⁻¹ᵁ chart d k) :
    rat φ k l = φ.stalkMap (genericPoint Z) ((PSpace ℂ d).presheaf.germ (chart d k) _ hk (ratioSec d k l)) := by
  unfold rat
  rw [dif_pos hk]
  exact (Scheme.Hom.germ_stalkMap_apply φ _ _ hk _).symm

end Overlap

open Overlap in

theorem rat_overlap : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (φ : Z ⟶ PSpace ℂ d) (a i j : Fin (d + 1)),
    genericPoint Z ∈ φ ⁻¹ᵁ chart d a → genericPoint Z ∈ φ ⁻¹ᵁ chart d i →
      rat φ a i ≠ 0 ∧ rat φ i j = rat φ a j / rat φ a i := by
  intro d Z _ φ a i j ha hi
  have hW : φ (genericPoint Z) ∈ Proj.basicOpen (homogeneousSubmodule (Fin (d + 1)) ℂ) (X a * X i) := by
    rw [Proj.basicOpen_mul]; exact ⟨ha, hi⟩
  let F := ((Proj.awayToSection (homogeneousSubmodule (Fin (d + 1)) ℂ) (X a * X i) ≫
    (PSpace ℂ d).presheaf.germ _ _ hW) ≫ φ.stalkMap (genericPoint Z)).hom
  have hA : ∀ l, rat φ a l = F (HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin (d + 1)) ℂ)
      (X_mem_one d i) (rfl : X a * X i = X a * X i) (awayRatio a l)) := by
    intro l
    rw [rat_eq_germ φ a l ha, ratioSec_eq, germ_awayToSection_mul a i rfl _ ha hW]
    rfl
  have hI : ∀ l, rat φ i l = F (HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin (d + 1)) ℂ)
      (X_mem_one d a) (mul_comm (X a) (X i)) (awayRatio i l)) := by
    intro l
    rw [rat_eq_germ φ i l hi, ratioSec_eq, germ_awayToSection_mul i a (mul_comm (X a) (X i)) _ hi hW]
    rfl
  have h1 : rat φ a i * rat φ i a = 1 := by
    rw [hA, hI, ← map_mul, awayRatio_mul_awayRatio, map_one]
  refine ⟨left_ne_zero_of_mul_eq_one h1, ?_⟩
  rw [div_eq_mul_inv, ← eq_inv_of_mul_eq_one_right h1, hI, hA, hI, ← map_mul, awayRatio_change]
end GlobalTheory.PD.XCover
