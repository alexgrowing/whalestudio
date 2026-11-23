import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCls

theorem carries_genericPt_of_isMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (Oz : Type) [CommRing Oz] (β : Oz →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (K : Type) [Field K] (φ : C.Y.Fn →+* K) (χ : c.F →+* K) (x : Sp K ⟶ Z.X) (g : EigFrame Z χ x), χ = φ.comp (constF e C.Y) → x = spMap φ ≫ genericPt C.Y ≫ C.π ≫ genι Z → C.f0.IsMap φ g → C.Carries (spMap φ ≫ genericPt C.Y) g := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z F _ e C K _ φ χ x g hχ hx hg
  have ha : @algebraMap (C.Y.X.presheaf.stalk (genericPoint C.Y.X)) C.Y.X.functionField _ _
      (stalkFunctionFieldAlgebra C.Y.X (genericPoint C.Y.X)) = RingHom.id _ :=
    congrArg CommRingCat.Hom.hom (C.Y.X.presheaf.stalkSpecializes_refl (genericPoint C.Y.X))
  refine ⟨genericPoint C.Y.X, φ, constF e C.Y, C.f0, 1, 1, rfl, ?_, hg.tri hχ hx⟩
  rw [ha]
  exact C.f0.tri_refl

end GlobalTheory.FlagCls

end
