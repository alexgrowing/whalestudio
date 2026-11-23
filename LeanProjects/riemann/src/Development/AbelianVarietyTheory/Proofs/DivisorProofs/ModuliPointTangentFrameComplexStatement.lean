import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliPointTangentFrameComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moduli_point_tangent_frame_complex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) (R : Type) [CommRing R] (x : Sp R ⟶ Z.X) (τ : E →+* ℂ) (g : ℕ) (e : Fin g → (Sp (DualNumber R) ⟶ Z.t.G.left)), GlobalTheory.LineNorm.IsTanBasis Z.t x e → ∃ (D : ℕ) (P : Matrix (Fin g) (Fin g) R), D ≠ 0 ∧ IsEigProj Z x τ e D P ∧ ∀ (K : Type) [Field K] [CharZero K] (ψ : R →+* K), (P.map ψ).rank = Dw.mult τ := by
  first | exact @GlobalTheory.ArLieBase.exists_isEigProj | exact GlobalTheory.ArLieBase.exists_isEigProj | (intros; apply GlobalTheory.ArLieBase.exists_isEigProj <;> assumption)
