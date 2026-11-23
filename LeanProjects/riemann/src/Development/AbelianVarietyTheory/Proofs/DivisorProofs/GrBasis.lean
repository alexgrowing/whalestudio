import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocGrLat
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

def GrBasis {R : Type} [CommRing R] (x : Sp R ⟶ Z.X) (τ : E →+* ℂ) (r : ℕ) : Prop :=
  ∃ (N : ℕ) (u : Fin r → (Sp (DualNumber R) ⟶ Z.t.G.left)), N ≠ 0 ∧
    (∀ (K : Type) [CommRing K] (ψ : R →+* K) (φ : c.F →+* K), spMap ψ ≫ x ≫ Z.s = spMap (φ.comp β) →
      IsEigBasis Z φ (spMap ψ ≫ x) τ (fun i => spMap (dualMap ψ) ≫ u i)) ∧
    ∀ (p : ℕ) [Fact p.Prime] (ψ : R →+* ↥(intO ℂ_[p])) (φ : c.F →+* ℂ_[p]),
      spMap ((intO ℂ_[p]).subtype.comp ψ) ≫ x ≫ Z.s = spMap (φ.comp β) →
        ∀ w, IsEigTan Z φ (spMap ((intO ℂ_[p]).subtype.comp ψ) ≫ x) τ w →
          ((∃ a : Fin r → ℂ_[p], (∀ i, ‖(N : ℂ_[p]) * a i‖ ≤ 1) ∧
              IsCombAtG Z.t (spMap ((intO ℂ_[p]).subtype.comp ψ) ≫ x)
                (fun i => spMap (dualMap ((intO ℂ_[p]).subtype.comp ψ)) ≫ u i) a w) ↔
            InGr Z φ (spMap ((intO ℂ_[p]).subtype.comp ψ) ≫ x)
              (latDR Z.t (spMap ((intO ℂ_[p]).subtype.comp ψ) ≫ x)) τ w)

end GlobalTheory.TwoLat

end
