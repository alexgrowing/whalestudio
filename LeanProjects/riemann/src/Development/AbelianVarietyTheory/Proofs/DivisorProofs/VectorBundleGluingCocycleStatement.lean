import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleGluingCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vector_bundle_gluing_cocycle : ∀ (X : Scheme.{0}) (r : ℕ) (ι : Type) (U : ι → X.Opens) (A : ∀ i j, Matrix (Fin r) (Fin r) Γ(X, U i ⊓ U j)), (∀ x : X, ∃ i, x ∈ U i) → (∀ i, A i i = 1) → (∀ (i j k : ι) (V : X.Opens) (hij : V ≤ U i ⊓ U j) (hjk : V ≤ U j ⊓ U k) (hik : V ≤ U i ⊓ U k), (A i j).map (resG X hij) * (A j k).map (resG X hjk) = (A i k).map (resG X hik)) → ∃ (M : X.Modules) (f : ∀ i, Fin r → Γ(M, U i)) (hf : ∀ i, VB.IsFrame (f i)), ∀ i j b a, trCo (hf i) (f j) b a = A i j b a := by
  first | exact @GlobalTheory.MatrixCocycle.exists_frames | exact GlobalTheory.MatrixCocycle.exists_frames | (intros; apply GlobalTheory.MatrixCocycle.exists_frames <;> assumption)
