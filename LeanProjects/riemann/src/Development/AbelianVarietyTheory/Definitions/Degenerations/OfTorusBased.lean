import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section
namespace GlobalTheory.ZJ
variable {S : Scheme.{0}} {H : Over S} [GrpObj H]

def Charts.InK (C : Charts H.left) (a : {i // C.wt i = C.c₀}) {Y : Over S} (k : Y ⟶ H) : Prop :=
  ∃ (h : ⊤ ≤ k.left ⁻¹ᵁ C.W a) (h₁ : ⊤ ≤ (1 : Y ⟶ H).left ⁻¹ᵁ C.W a), ∀ j, C.wt j = C.c₀ →
    (k.left.appLE _ ⊤ h).hom (C.r a j) = ((1 : Y ⟶ H).left.appLE _ ⊤ h₁).hom (C.r a j)

def Charts.Based (C : Charts H.left) {d : ℕ} (c : Fin d → C.Cl) (a : {i // C.wt i = C.c₀}) (j : Fin d → C.I) : Prop :=
  ⊤ ≤ eSec H ⁻¹ᵁ C.W a ∧ ∀ n, C.wt (j n) = c n ∧ ⊤ ≤ eSec H ⁻¹ᵁ H.left.basicOpen (C.r a (j n))

def Charts.KerIs (C : Charts H.left) {d : ℕ} (a : {i // C.wt i = C.c₀}) (j : Fin d → C.I)
    (i : splitTorus S (Fin d → ℤ) ⟶ H) : Prop :=
  Mono i ∧ (∀ (Y : Over S) (k : Y ⟶ H), C.InK a k ↔ ∃ t, k = t ≫ i) ∧
    ∀ (Y : Over S) (t : Y ⟶ splitTorus S (Fin d → ℤ)) (n : Fin d) (h : ⊤ ≤ (t ≫ i).left ⁻¹ᵁ C.W a)
      (h₁ : ⊤ ≤ (1 : Y ⟶ H).left ⁻¹ᵁ C.W a), ((t ≫ i).left.appLE _ ⊤ h).hom (C.r a (j n)) =
        t.left.appTop.hom (charUnit S (Fin d → ℤ) (Pi.single n 1)).val * ((1 : Y ⟶ H).left.appLE _ ⊤ h₁).hom (C.r a (j n))

private theorem appLE_univ_univ_apply_eq_appTop {X Y : Scheme.{0}} (g : Y ⟶ X) (h : ⊤ ≤ g ⁻¹ᵁ (⊤ : X.Opens)) :
    g.appLE ⊤ ⊤ h = g.appTop := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

end GlobalTheory.ZJ
end
