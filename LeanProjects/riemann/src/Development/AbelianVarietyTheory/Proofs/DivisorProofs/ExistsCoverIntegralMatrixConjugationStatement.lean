import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoverIntegralMatrixConjugation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cover_integral_matrix_conjugation : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (C : CxSt F) (N : ℕ) (A A' : Fin N → Adl C Y) (p n k : ℕ), p.Prime → (∀ i, (A' i).D = (A i).D) → RelFlag A A' p n k → ∃ (V : Cover Y) (M M' : V.X → Matrix (Fin N) (Fin N) V.X.functionField) (c c' : V.X → Fin N → V.X.functionFieldˣ) (P Q : Matrix (Fin N) (Fin N) V.X.functionField), P * Q = 1 ∧ (∀ i j, IsIntegral ℤ ((n : V.X.functionField) * P i j) ∧ IsIntegral ℤ ((n : V.X.functionField) * Q i j)) ∧ Cross p k M M' c c' P ∧ ∀ i, Reads V p (A i) (fun x => c x i) ∧ Reads V p (A' i) fun x => c' x i := by
  first | exact @GlobalTheory.LatChain.exists_cross_of_relFlag | exact GlobalTheory.LatChain.exists_cross_of_relFlag | (intros; apply GlobalTheory.LatChain.exists_cross_of_relFlag <;> assumption)
