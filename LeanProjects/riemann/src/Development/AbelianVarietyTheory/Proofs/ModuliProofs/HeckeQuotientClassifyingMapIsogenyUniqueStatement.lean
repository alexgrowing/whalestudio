import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeQuotientClassifyingMapIsogenyUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeQuotient_classifyingMap_isogeny_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (o o₁ o₂ : Ob D l s) (ψ₁ : o.t.G ⟶ o₁.t.G) (ψ₂ : o.t.G ⟶ o₂.t.G) (K : Set o.t.G.left) (f₁ f₂ : S ⟶ Xo.X) (n₁ : ObjMap o₁ Xo.univ f₁) (n₂ : ObjMap o₂ Xo.univ f₂), admitted l 𝔓 p → HeckeSet D o.t 𝔓 p i K → f₁ ≫ Xo.s = s → f₂ ≫ Xo.s = s → IsIsog o o₁ p ψ₁ → IsIsog o o₂ p ψ₂ → KerSet ψ₁ K → KerSet ψ₂ K → f₁ = f₂ ∧ ψ₁.left ≫ n₁.toSABMap.φ = ψ₂.left ≫ n₂.toSABMap.φ := by
  first | exact @GlobalTheory.heckeQuot_unique | exact GlobalTheory.heckeQuot_unique | (intros; apply GlobalTheory.heckeQuot_unique <;> assumption)
