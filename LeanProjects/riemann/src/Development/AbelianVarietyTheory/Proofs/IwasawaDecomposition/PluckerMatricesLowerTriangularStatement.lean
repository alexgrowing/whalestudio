import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerMatricesLowerTriangular
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNonzeroLocusSecOfRat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerNonzeroIffIndependent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCoordNeZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.plucker_matrices_lower_triangular : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (K : Type) [Field K] (M M' : GlobalTheory.FlagBundle.Mat S.Dw.mult K), (∀ τ, IsUnit (M τ).det) → (∀ τ, IsUnit (M' τ).det) → (∀ x : GlobalTheory.FlagAmple.Step S.Dw, ∃ u : Kˣ, GlobalTheory.FlagAmple.PlkLoc.plkFn M x = (u : K) • GlobalTheory.FlagAmple.PlkLoc.plkFn M' x) → ∀ τ, ∃ L : Matrix (Fin (S.Dw.mult τ)) (Fin (S.Dw.mult τ)) K, M τ = L * M' τ ∧ ∀ i l, i < l → L i l = 0 := by
  first | exact @GlobalTheory.FlagAmple.PlkLoc.LowerTri.eq_lower_mul_of_plk_prop | exact GlobalTheory.FlagAmple.PlkLoc.LowerTri.eq_lower_mul_of_plk_prop | (intros; apply GlobalTheory.FlagAmple.PlkLoc.LowerTri.eq_lower_mul_of_plk_prop <;> assumption)
