import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHeckeQuotientReducedBase
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_heckeQuotient_reducedBase : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (KA l)) (o : Ob D l s) (C : Over S) (j : C ⟶ o.t.G), 1 ≤ D.p + D.q → admitted l 𝔓 p → IsReduced S → IsFinite C.hom → Etale C.hom → IsClosedImmersion j.left → HeckeSet D o.t 𝔓 p i (Set.range j.left) → ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ∧ ∃ (o' : Ob D l s) (_ : ObjMap o' Xo.univ f) (ψ : o.t.G ⟶ o'.t.G), IsIsog o o' p ψ ∧ IsPullback j (toUnit C) ψ η[o'.t.G] := by
  first | exact @GlobalTheory.HkFam.existsUnique_heckeQuot | exact GlobalTheory.HkFam.existsUnique_heckeQuot | (intros; apply GlobalTheory.HkFam.existsUnique_heckeQuot <;> assumption)
