import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixInductionTransvectionDiagonal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecOfSpec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factors_through_zero_locus : ∀ (Rg : Type) [CommRing Rg] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) Rg)) (T : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin n) Rg)), (∃ w : T ⟶ Sp (MvPolynomial (Fin n) Rg ⧸ I), w ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = g) ↔ ∀ P ∈ I, GlobalTheory.FormsLocus.ringOf g P = 0 := by
  first | (exact @GlobalTheory.FormsLocus.factors_quot_iff) | (exact GlobalTheory.FormsLocus.factors_quot_iff) | (intros; apply GlobalTheory.FormsLocus.factors_quot_iff  <;> assumption)
