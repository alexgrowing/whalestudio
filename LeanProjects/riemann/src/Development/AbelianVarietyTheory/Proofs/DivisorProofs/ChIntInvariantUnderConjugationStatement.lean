import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChIntInvariantUnderConjugation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualRef
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chInt_invariant_under_conjugation : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsProjOver p → ∀ (N : HermLB p) (D : ℕ) (f f' : ∀ σ : k →+* ℂ, CxPts p σ → ℝ), (∀ (σ σ' : k →+* ℂ) (y : CxPts p σ) (y' : CxPts p σ'), y'.1 = spMap (starRingEnd ℂ) ≫ y.1 → f' σ' y' = f σ y) → chInt N D f' = chInt N D f := by
  first | exact @GlobalTheory.ArInt.chInt_conj | exact GlobalTheory.ArInt.chInt_conj | (intros; apply GlobalTheory.ArInt.chInt_conj <;> assumption)
