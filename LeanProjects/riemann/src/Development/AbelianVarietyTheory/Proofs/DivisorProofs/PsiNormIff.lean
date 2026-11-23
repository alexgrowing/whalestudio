import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH
open scoped CategoryTheory.Obj
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnifTorsK

def PsiNormAt (p : ℕ) [Fact p.Prime] {V : Type} [CommRing V] [IsDomain V] [Algebra (FractionRing V) (PadicAlgCl p)]
    (D : DegPre V) (χ : D.X) (r : ℝ) : Prop :=
  ∀ j : PUnit → D.P.L.ι, ⊤ ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit) →
    ‖algebraMap (FractionRing V) (PadicAlgCl p) (valF (𝟙 (Sp (FractionRing V))) _ ((D.psi χ).s j).val)‖ = r

theorem psiNorm_iff {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ}
    [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) (χ : u.D.toPre.X) (r : ℝ) :
    u.PsiNorm χ r ↔ PsiNormAt p u.D.toPre χ r := Iff.rfl

end GlobalTheory.UnifTorsK
