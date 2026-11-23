import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
open Limits MonoidalCategory CartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PPAS

def IsProd {S : Scheme.{0}} (P P₁ P₂ : PPAS S) : Prop :=
  ∃ (π₁ : P.A ⟶ P₁.A) (π₂ : P.A ⟶ P₂.A), IsMonHom π₁ ∧ IsMonHom π₂ ∧
    Nonempty (IsLimit (BinaryFan.mk π₁ π₂)) ∧ P.g = P₁.g + P₂.g ∧
    P.c = CechPic.pull (π₁ ⊗ₘ π₁).left P₁.c + CechPic.pull (π₂ ⊗ₘ π₂).left P₂.c

theorem IsProd.g_eq {S : Scheme.{0}} {P P₁ P₂ : PPAS S} (h : P.IsProd P₁ P₂) : P.g = P₁.g + P₂.g := by
  obtain ⟨_, _, _, _, _, hg, _⟩ := h
  exact hg

end GlobalTheory.PPAS
