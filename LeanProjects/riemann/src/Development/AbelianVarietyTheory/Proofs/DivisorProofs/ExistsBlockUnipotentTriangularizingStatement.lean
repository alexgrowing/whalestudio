import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockUnipotentTriangularizing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUniOne
open NumberField CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.TrueGeo
open GlobalTheory.LieVB (omega)
open GlobalTheory.LocM (tanEv)
open Formalism.MainNotions.DIV.Cons (intO)
open scoped Classical
open GlobalTheory.LieFilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_block_unipotent_triangularizing : ∀ {R : Type} [CommRing R] {κ : Type} [Fintype κ] (bl : κ → ℕ) {g : ℕ} (P : Matrix (Fin g) κ R) (w : κ ≃ Fin g),
    (∀ k : ℕ, IsUnit (minor bl w k P)) →
    ∃ Q : Matrix κ κ R, BlockUni bl Q ∧ Q.det = 1 ∧ ∀ z z', bl z < bl z' → (P * Q) (w z) z' = 0 := by
  first | exact @GlobalTheory.LieFilt.exists_blockUni_mul_eq_zero | exact GlobalTheory.LieFilt.exists_blockUni_mul_eq_zero | (intros; apply GlobalTheory.LieFilt.exists_blockUni_mul_eq_zero <;> assumption)
