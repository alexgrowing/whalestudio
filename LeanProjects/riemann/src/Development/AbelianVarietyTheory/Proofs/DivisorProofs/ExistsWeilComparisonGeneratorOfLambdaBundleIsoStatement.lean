import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilComparisonGeneratorOfLambdaBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpL
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.Mum.Two.WeilCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilComparisonGenerator_of_lambdaBundleIso : ∀ (S : Scheme.{0}) (P₀ P₁ P₂ : PolAV S) (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A), LBIso (cubeLB P₁.A ![fst P₀.A P₀.A ≫ f₁, snd P₀.A P₀.A ≫ g₁] P₁.L) (cubeLB P₂.A ![fst P₀.A P₀.A ≫ f₂, snd P₀.A P₀.A ≫ g₂] P₂.L) → ∃ u : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂), u.IsGen := by
  first | exact @GlobalTheory.Mum.Two.WeilCmp.exists_cmpGen_of_lbIso | exact GlobalTheory.Mum.Two.WeilCmp.exists_cmpGen_of_lbIso | (intros; apply GlobalTheory.Mum.Two.WeilCmp.exists_cmpGen_of_lbIso <;> assumption)
