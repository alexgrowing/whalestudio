import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusCyclotomicPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_torus_cyclotomic_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (T : Scheme.{0}) [IsLocallyNoetherian T] (t : SAB H T), T.IsSeparated → ∀ (S : Finset ℕ), (∀ p ∈ S, p.Prime) → ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] (x : Sp R ⟶ T), (∃ ζ : K, IsPrimitiveRoot ζ (∏ p ∈ S, p)) → GlobalTheory.HtGen.SplitK t (spMap (algebraMap R K) ≫ x) (∏ p ∈ S, p) → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)), GlobalTheory.LineNorm.IsTanBasis t x e → ∃ (M : ℕ) (h : Fin M → Fin g → R), LatPres t x (ArIn.ind S) (fun _ => 0) e h := by
  first | exact @GlobalTheory.ArLieBase.latPres_of_splitK | exact GlobalTheory.ArLieBase.latPres_of_splitK | (intros; apply GlobalTheory.ArLieBase.latPres_of_splitK <;> assumption)
