import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilComparisonGeneratorNormalisedZeroSecti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpL
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.Mum.Two.WeilCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilComparisonGenerator_normalised_zeroSection : ∀ (S : Scheme.{0}) (P₀ P₁ P₂ : PolAV S) [Nonempty P₁.A.left] [Nonempty P₂.A.left] (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A) [IsMonHom f₁] [IsMonHom g₁] [IsMonHom f₂] [IsMonHom g₂], ∀ (u : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂)), u.IsGen → ∃ u' : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂), u'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ S) (z : Z) (J), Good (join P₁.L P₂.L) z J → val u' (r ≫ zero2 P₀.A) z J = 1 := by
  first | exact @GlobalTheory.Mum.Two.WeilCmp.exists_gen_nrm | exact GlobalTheory.Mum.Two.WeilCmp.exists_gen_nrm | (intros; apply GlobalTheory.Mum.Two.WeilCmp.exists_gen_nrm <;> assumption)
