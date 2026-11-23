import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LogGramSquareSmooth
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
open AlgebraicGeometry CategoryTheory Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CxPts GlobalTheory.GradedNorm
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_gram_square_smooth : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D m : ℕ} (R : AnRead p σ D) (S : Set (CxPts p σ)) (M : CxPts p σ → Matrix (Fin m) (Fin m) ℂ), (∀ a b, R.SmoothOn S (fun y => (M y a b).re) ∧ R.SmoothOn S (fun y => (M y a b).im)) → (∀ y ∈ S, (M y).PosDef) → ∀ i : Fin m, R.SmoothOn S (fun y => Real.log (grSq (M y) i)) := by
  first | exact @GlobalTheory.smoothOn_log_grSq | exact GlobalTheory.smoothOn_log_grSq | (intros; apply GlobalTheory.smoothOn_log_grSq <;> assumption)
