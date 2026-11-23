import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticModelFlagHeightFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_model_flag_height_first : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (Oz : Type) [CommRing Oz] (β : Oz →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (X W : Scheme.{0}) (jB : W ⟶ X) (πB : W ⟶ gen Z), IsAffineHom jB → IntCrit (πB ≫ genStr Z ≫ spMap e.toRingHom) jB → ∀ (r : ℕ) (τ : E →+* ℂ) (kind : ℕ → Bool) (U U' : X.Opens) (u : LocAssign Z r jB U) (u' : LocAssign Z r jB U'), IsAffineOpen (U ⊓ U') → IsLocFrame Z e jB πB r τ U u → IsLocFrame Z e jB πB r τ U' u' → IsLocLat Z e jB πB r τ kind U u → IsLocLat Z e jB πB r τ kind U' u' → ∃ A : Matrix (Fin r) (Fin r) Γ(X, U ⊓ U'), IsTrans Z jB πB u u' A := by
  first | exact @GlobalTheory.ArLieBase.exists_isTrans | exact GlobalTheory.ArLieBase.exists_isTrans | (intros; apply GlobalTheory.ArLieBase.exists_isTrans <;> assumption)
