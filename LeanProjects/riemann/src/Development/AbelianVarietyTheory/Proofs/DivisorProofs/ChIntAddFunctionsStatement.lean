import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChIntAddFunctions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualRef
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chInt_add_functions : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p) (n : ι → ℤ) (f g : ∀ σ : k →+* ℂ, CxPts p σ → ℝ), (∀ σ, Continuous (f σ)) → (∀ σ, Continuous (g σ)) → chInt (ArInt.comb L n) D (fun σ y => f σ y + g σ y) = chInt (ArInt.comb L n) D f + chInt (ArInt.comb L n) D g := by
  first | exact @GlobalTheory.Mean4.chInt_add_of_continuous | exact GlobalTheory.Mean4.chInt_add_of_continuous | (intros; apply GlobalTheory.Mean4.chInt_add_of_continuous <;> assumption)
