import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory.AbLaw

namespace GlobalTheory.FormalAlg

variable {R : Type} [CommRing R] {W : Scheme.{0}}

def baseIdeal (f : W ⟶ Spec (CommRingCat.of R)) (J : Ideal R) : W.IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (J.map (cst f ⊤))

theorem baseIdeal_ideal (f : W ⟶ Spec (CommRingCat.of R)) (J : Ideal R) (U : W.affineOpens) :
    (baseIdeal f J).ideal U = J.map (cst f U.1) := by
  rw [baseIdeal, Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_map]
  congr 1
  ext r
  exact rs_cst f le_top r

def IsSystem (f : W ⟶ Spec (CommRingCat.of R)) (I : Ideal R) (t : ℕ → W.IdealSheafData) : Prop :=
  ∀ e, t e = t (e + 1) ⊔ baseIdeal f (I ^ (e + 1))

def Reduces (f : W ⟶ Spec (CommRingCat.of R)) (I : Ideal R) (T : W.IdealSheafData)
    (t : ℕ → W.IdealSheafData) : Prop :=
  ∀ e, T ⊔ baseIdeal f (I ^ (e + 1)) = t e

def Alg (f : W ⟶ Spec (CommRingCat.of R)) (I : Ideal R) : Prop :=
  ∀ t : ℕ → W.IdealSheafData, IsSystem f I t → (∀ e, IsProper ((t e).subschemeι ≫ f)) →
    ∃ T : W.IdealSheafData, IsProper (T.subschemeι ≫ f) ∧ Reduces f I T t

theorem IsSystem.baseIdeal_le {f : W ⟶ Spec (CommRingCat.of R)} {I : Ideal R}
    {t : ℕ → W.IdealSheafData} (h : IsSystem f I t) (e : ℕ) : baseIdeal f (I ^ (e + 1)) ≤ t e := by
  rw [h e]
  exact le_sup_right

end GlobalTheory.FormalAlg
