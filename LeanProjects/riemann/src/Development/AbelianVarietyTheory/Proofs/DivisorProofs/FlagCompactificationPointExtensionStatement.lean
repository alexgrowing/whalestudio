import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCompactificationPointExtension
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_compactification_point_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (Oz : Type) [CommRing Oz] (β : Oz →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (K : Type) [Field K] (χ : c.F →+* K) (x : Sp K ⟶ Z.X) (g : EigFrame Z χ x) (K' : Type) [Field K'] (ψ : K →+* K') (χ' : c.F →+* K') (x' : Sp K' ⟶ Z.X) (g' : EigFrame Z χ' x') (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → K'ˣ) (p : Sp K ⟶ C.Y.X), x = p ≫ C.π ≫ genι Z → p ≫ C.π ≫ genStr Z = spMap χ → g.Tri ψ g' t → (C.Carries (spMap ψ ≫ p) g' ↔ C.Carries p g) := by
  first | exact @GlobalTheory.FlagCls.CarryBC.carries_baseChange_iff | exact GlobalTheory.FlagCls.CarryBC.carries_baseChange_iff | (intros; apply GlobalTheory.FlagCls.CarryBC.carries_baseChange_iff <;> assumption)
