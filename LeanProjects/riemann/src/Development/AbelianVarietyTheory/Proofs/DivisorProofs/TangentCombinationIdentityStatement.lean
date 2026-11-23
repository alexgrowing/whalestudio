import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentCombinationIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_combination_identity : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz] {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {K : Type} [CommRing K] (φ : c.F →+* K) (y : Sp K ⟶ Z.X) (τ : E →+* ℂ) {m : ℕ} (u w : Fin m → (Sp (DualNumber K) ⟶ Z.t.G.left)) (P Q : Matrix (Fin m) (Fin m) K), IsEigBasis Z φ y τ u → (∀ a, IsCombAtG Z.t y u (fun b => P a b) (w a)) → Q * P = 1 → IsEigBasis Z φ y τ w := by
  first | exact @GlobalTheory.ArLieBase.isEigBasis_of_mul_eq_one | exact GlobalTheory.ArLieBase.isEigBasis_of_mul_eq_one | (intros; apply GlobalTheory.ArLieBase.isEigBasis_of_mul_eq_one <;> assumption)
