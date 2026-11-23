import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocGrLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFlagged
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwoLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β)

def IsCoordMat {X W : Scheme.{0}} (jB : W ⟶ X) (πB : W ⟶ gen Z) {M M' : X.Modules} {r : ℕ}
    (t : FrAssign Z M r jB) (t' : FrAssign Z M' r jB) {V : X.Opens} {f : Fin r → Γ(M, V)} (hf : VB.IsFrame f)
    {f' : Fin r → Γ(M', V)} (hf' : VB.IsFrame f') (A : Matrix (Fin r) (Fin r) Γ(X, V)) : Prop :=
  ∀ (K : Type) [CommRing K] (x : Sp K ⟶ W) (hx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ V) (i : Fin r),
    IsCombAtG Z.t (x ≫ πB ≫ genι Z) (t' V f' hf' K x hx)
      (fun b => TangentOrigin.evalPt (x ≫ jB) V hx (A b i)) (t V f hf K x hx i)

end GlobalTheory.TwoLat

end
