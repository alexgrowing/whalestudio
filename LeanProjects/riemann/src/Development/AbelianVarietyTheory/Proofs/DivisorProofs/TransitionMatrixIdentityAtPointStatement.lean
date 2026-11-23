import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransitionMatrixIdentityAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transition_matrix_identity_at_point : ∀ {X : Scheme.{0}} {M : X.Modules} {r : ℕ} {U : X.Opens} {f : Fin r → Γ(M, U)} (hf : VB.IsFrame f) {K : Type} [CommRing K] (x : Sp K ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ (U ⊓ U)) (c a : Fin r), TangentOrigin.evalPt x _ h (trCo hf f c a) = if c = a then 1 else 0 := by
  first | exact @GlobalTheory.ArLieBase.evalPt_trCo_self | exact GlobalTheory.ArLieBase.evalPt_trCo_self | (intros; apply GlobalTheory.ArLieBase.evalPt_trCo_self <;> assumption)
