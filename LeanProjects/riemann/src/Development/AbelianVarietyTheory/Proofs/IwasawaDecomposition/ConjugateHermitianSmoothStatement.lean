import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateHermitianSmooth
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
open AlgebraicGeometry CategoryTheory Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CxPts GlobalTheory.GradedNorm
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_hermitian_smooth : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D m : ℕ} (R : AnRead p σ D) (S : Set (CxPts p σ)), IsOpen S → ∀ (A M : CxPts p σ → Matrix (Fin m) (Fin m) ℂ), (∀ a b, R.HoloOn S (fun y => A y a b)) → (∀ a b, R.SmoothOn S (fun y => (M y a b).re) ∧ R.SmoothOn S (fun y => (M y a b).im)) → ∀ a b : Fin m, R.SmoothOn S (fun y => (((A y)ᴴ * M y * A y) a b).re) ∧ R.SmoothOn S (fun y => (((A y)ᴴ * M y * A y) a b).im) := by
  first | exact @GlobalTheory.AnRead.smoothOn_conjTranspose_mul_mul | exact GlobalTheory.AnRead.smoothOn_conjTranspose_mul_mul | (intros; apply GlobalTheory.AnRead.smoothOn_conjTranspose_mul_mul <;> assumption)
