import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SortSign

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PD.XCover

attribute [local instance] MvPolynomial.gradedAlgebra

variable (d : ℕ)

theorem X_mem_one (i : Fin (d + 1)) : (X i : MvPolynomial (Fin (d + 1)) ℂ) ∈ homogeneousSubmodule (Fin (d + 1)) ℂ 1 :=
  isHomogeneous_X ℂ i

abbrev chart (i : Fin (d + 1)) : (PSpace ℂ d).Opens := Proj.basicOpen (homogeneousSubmodule (Fin (d + 1)) ℂ) (X i)

def ratioSec (i j : Fin (d + 1)) : Γ(PSpace ℂ d, chart d i) :=
  Proj.awayToSection (homogeneousSubmodule (Fin (d + 1)) ℂ) (X i)
    (Away.mk (homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d i) 1 (X j) (by simpa using X_mem_one d j))

variable {d} {Z : Scheme.{0}} [IsIntegral Z]

open Classical in

def rat (φ : Z ⟶ PSpace ℂ d) (i j : Fin (d + 1)) : Z.functionField :=
  if h : genericPoint Z ∈ φ ⁻¹ᵁ chart d i then
    Z.presheaf.germ (φ ⁻¹ᵁ chart d i) (genericPoint Z) h (φ.app (chart d i) (ratioSec d i j))
  else 0

variable [Algebra ℂ Z.functionField]

def fld (φ : Z ⟶ PSpace ℂ d) : IntermediateField ℂ Z.functionField := IntermediateField.adjoin ℂ (Set.range (rat φ 0))

def crd (φ : Z ⟶ PSpace ℂ d) : Fin (d + 1) → fld φ := fun j =>
  ⟨rat φ 0 j, IntermediateField.subset_adjoin ℂ _ ⟨j, rfl⟩⟩

theorem crd_val (φ : Z ⟶ PSpace ℂ d) (j : Fin (d + 1)) : ((crd φ j : fld φ) : Z.functionField) = rat φ 0 j := rfl

end GlobalTheory.PD.XCover
