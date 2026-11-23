import Mathlib
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

def IsLocGrLat {F : Type} [Field F] [NumberField F] (e : F ≃+* c.F) {X W : Scheme.{0}} (jB : W ⟶ X) (πB : W ⟶ gen Z)
    (r : ℕ) (τ : E →+* ℂ) (U : X.Opens) (u : LocAssign Z r jB U) : Prop :=
  ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (hp : (resP v).Prime) (ε : TrueGeo.Ext v)
    (xg : Sp (AlgebraicClosure F) ⟶ W) (xt : Sp ε.O ⟶ X),
    xg ≫ πB ≫ genStr Z ≫ spMap e.toRingHom = spMap (algebraMap F (AlgebraicClosure F)) →
    spMap ε.O.subtype ≫ xt = xg ≫ jB → ⊤ ≤ xt ⁻¹ᵁ U → ∀ (hx : ⊤ ≤ (xg ≫ jB) ⁻¹ᵁ U),
      haveI : Fact (resP v).Prime := ⟨hp⟩
      ∀ w, IsEigTan Z (((ioOf (resP v) ε).comp (algebraMap F (AlgebraicClosure F))).comp e.symm.toRingHom)
          (spMap (ioOf (resP v) ε) ≫ xg ≫ πB ≫ genι Z) τ w →
        ((∃ a : Fin r → ℂ_[resP v], (∀ i, ‖a i‖ ≤ 1) ∧
            IsCombAtG Z.t (spMap (ioOf (resP v) ε) ≫ xg ≫ πB ≫ genι Z)
              (fun i => spMap (dualMap (ioOf (resP v) ε)) ≫ u _ xg hx i) a w) ↔
          InGr Z (((ioOf (resP v) ε).comp (algebraMap F (AlgebraicClosure F))).comp e.symm.toRingHom)
            (spMap (ioOf (resP v) ε) ≫ xg ≫ πB ≫ genι Z)
            (latDR Z.t (spMap (ioOf (resP v) ε) ≫ xg ≫ πB ≫ genι Z)) τ w)

end GlobalTheory.TwoLat

end
