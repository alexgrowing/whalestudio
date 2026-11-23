import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem exists_pat_of_obj :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), ∃ T : PAT H S, T.t = o.t ∧ T.g = Module.finrank ℚ E / 2 * (D.p + D.q) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ o =>
    ⟨⟨o.t, ObjDim.isAbelianScheme o, _, ObjDim.smoothOfRelativeDimension o, ObjDim.sym, o.ample, o.ktriv⟩, rfl, rfl⟩

end GlobalTheory.CM
