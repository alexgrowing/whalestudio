import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransitionCocycleAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transition_cocycle_at_point : ∀ {X : Scheme.{0}} {M : X.Modules} {r : ℕ} {U₁ U₂ U₃ : X.Opens} {f₁ : Fin r → Γ(M, U₁)} {f₂ : Fin r → Γ(M, U₂)} (h₁ : VB.IsFrame f₁) (h₂ : VB.IsFrame f₂) (f₃ : Fin r → Γ(M, U₃)) {K : Type} [CommRing K] (x : Sp K ⟶ X) (h₁₂ : ⊤ ≤ x ⁻¹ᵁ (U₁ ⊓ U₂)) (h₂₃ : ⊤ ≤ x ⁻¹ᵁ (U₂ ⊓ U₃)) (h₁₃ : ⊤ ≤ x ⁻¹ᵁ (U₁ ⊓ U₃)) (c a : Fin r), ∑ b, TangentOrigin.evalPt x _ h₁₂ (trCo h₁ f₂ c b) * TangentOrigin.evalPt x _ h₂₃ (trCo h₂ f₃ b a) = TangentOrigin.evalPt x _ h₁₃ (trCo h₁ f₃ c a) := by
  first | exact @GlobalTheory.ArLieBase.trCo_chain | exact GlobalTheory.ArLieBase.trCo_chain | (intros; apply GlobalTheory.ArLieBase.trCo_chain <;> assumption)
