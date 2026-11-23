import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBasisOnAny
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushInvertibleOfDensePart
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.PushInv

theorem pushInvertible_of_model : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B F O : Type) [CommRing B] [Field F] [CommRing O] (b : Base l B) (U : Scheme.{0}) (s : U ⟶ Sp B) (o : Obj D l b s) (c : U ⟶ Sp F) (β : O →+* F) (C : Cpt c o.t β), IsDedFrac β → HasTheta C.t.G C.t.PP.L → PushInvertible C.t.G C.t.PP.L := by
  intro hL hL2 hL3 E _ _ _ H D l B F O _ _ _ b U s o c β C hβ hθ
  have hS : Out.SecBaseChangeAnySt := by cases hL; cases hL2; cases hL3; assumption
  have hH : Out.GlobalSectionsRankAlgClosed := by cases hL; cases hL2; cases hL3; assumption
  obtain ⟨⟨hDom, hDed⟩, -, hFr⟩ := hβ
  let _ : Algebra O F := β.toAlgebra
  obtain ⟨hN, -, -, hPre, hFl, hDo, hQC⟩ :=
    GlobalTheory.genericPart_dense_proOpen O F C.X U C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
  have hPB : IsPullback C.m.φ o.t.G.hom C.t.G.hom (C.jQ ≫ pullback.fst C.s (spMap β)) := C.m.cart.1
  obtain ⟨w, hw, -⟩ := C.m.lin
  have hIso : LBIso o.t.PP.L (C.t.PP.L.pull C.m.φ) := ⟨w, hw⟩
  have hSm : Smooth C.t.G.hom := by
    have sa := C.t.semi
    first | infer_instance | exact sa.1 | (cases sa; assumption)
  have hGI : GeometricallyIntegral C.t.G.hom := by
    have sa := C.t.semi
    have _ := hSm
    have _ : GeometricallyConnected C.t.G.hom := by
      first | infer_instance | (cases sa; assumption)
    exact GlobalTheory.grpObj_geometricallyIntegral_of_smooth C.X C.t.G
  exact @GlobalTheory.PushInv.pushInvertible_of_densePart C.X U hN (C.jQ ≫ pullback.fst C.s (spMap β)) C.normal hPre hFl hDo hQC
    C.t.G o.t.G C.m.φ C.t.PP.L o.t.PP.L hSm hGI hPB C.t.PP.isLB o.t.PP.isLB hIso
    (GlobalTheory.PushInv.pushInvertible_any hS hH U (GlobalTheory.Obj.toPolAV o)) hθ

end GlobalTheory.PushInv
