import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliTangentFrameBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moduli_tangent_frame_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (Oz : Type) [CommRing Oz] (β : Oz →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (R R' : Type) [CommRing R] [CommRing R'] (ψ : R →+* R') (x : Sp R ⟶ Z.X) (τ : E →+* ℂ) (kind : ℕ → Bool) (sc : ℕ → ℝ) (g M r D N : ℕ) (e : Fin g → (Sp (DualNumber R) ⟶ Z.t.G.left)) (h : Fin M → Fin g → R) (P : Matrix (Fin g) (Fin g) R) (U : Matrix (Fin g) (Fin r) R') (I : Fin r → Fin M), D ≠ 0 → N ≠ 0 → GlobalTheory.LineNorm.IsTanBasis Z.t x e → IsEigProj Z x τ e D P → LatPres Z.t x kind sc e h → IsSplitting D (P.map ψ) (fun j i => ψ (h j i)) N U I → RingBasis Z (spMap ψ ≫ x) τ r kind sc := by
  first | exact @GlobalTheory.ArLieBase.ringBasis_of_split | exact GlobalTheory.ArLieBase.ringBasis_of_split | (intros; apply GlobalTheory.ArLieBase.ringBasis_of_split <;> assumption)
