import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalModelFiniteCoverNormal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocGrLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toroidal_model_finite_cover_normal : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
    {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {F : Type} [Field F] [NumberField F] (e : F ≃+* c.F)
    {X W : Scheme.{0}} (jB : W ⟶ X) (πB : W ⟶ gen Z) (ρ : X ⟶ Z.X), jB ≫ ρ = πB ≫ genι Z →
    ∀ (U : X.Opens) (hU : IsAffineOpen U) (τ : E →+* ℂ) (r : ℕ),
    GlobalTheory.TwoLat.GrBasis Z (R := Γ(X, U)) (hU.fromSpec ≫ ρ) τ r →
    ∃ u : LocAssign Z r jB U, IsLocFrame Z e jB πB r τ U u ∧ GlobalTheory.TwoLat.IsLocGrLat Z e jB πB r τ U u := by
  first | exact @GlobalTheory.TwoLat.exists_locFrame_of_grBasis | exact GlobalTheory.TwoLat.exists_locFrame_of_grBasis | (intros; apply GlobalTheory.TwoLat.exists_locFrame_of_grBasis <;> assumption)
