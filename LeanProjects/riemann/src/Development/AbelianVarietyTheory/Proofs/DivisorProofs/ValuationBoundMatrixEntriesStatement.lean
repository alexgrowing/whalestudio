import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationBoundMatrixEntries
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.Vert GlobalTheory.TriFrame GlobalTheory.FlagCell
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_bound_matrix_entries : ∀ (R K : Type) [CommRing R] [IsLocalRing R] [Field K] [Algebra R K] (ι : Type) (C : ι → Type) [∀ t, NontriviallyNormedField (C t)] [∀ t, IsUltrametricDist (C t)] (θ : ∀ t, K →+* C t), (∀ t a, ‖θ t (algebraMap R K a)‖ ≤ 1) → (∀ κ : K, (∀ t, ‖θ t κ‖ ≤ 1) → ∃ a, algebraMap R K a = κ) → (∃ t, ∀ a ∈ maximalIdeal R, ‖θ t (algebraMap R K a)‖ < 1) → ∀ (r : ℕ) (M : Matrix (Fin r) (Fin r) K) (ρ : Fin r → K), (∀ t i, ‖θ t (ρ i)‖ * matNorm (M.map (θ t)) i = 1) → ∃ P : GL (Fin r) R, (∀ l j, j < l → ((P : Matrix (Fin r) (Fin r) R).map (algebraMap R K) * M) l j = 0) ∧ ∀ j, ((P : Matrix (Fin r) (Fin r) R).map (algebraMap R K) * M) j j * ρ j = 1 := by
  first | exact @GlobalTheory.TriFrame.exists_gl_upperTri_of_matNorm | exact GlobalTheory.TriFrame.exists_gl_upperTri_of_matNorm | (intros; apply GlobalTheory.TriFrame.exists_gl_upperTri_of_matNorm <;> assumption)
