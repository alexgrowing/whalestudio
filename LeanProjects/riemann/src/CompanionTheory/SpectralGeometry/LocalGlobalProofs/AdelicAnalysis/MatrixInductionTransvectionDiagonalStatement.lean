import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MatrixInductionTransvectionDiagonal
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_induction_transvection_diagonal : ∀ (R : Type) [CommRing R], (∀ a b : R, IsCoprime a b → ∃ t, IsUnit (a + t * b)) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (p : Matrix ι ι R → Prop), (∀ (i j : ι) (c : R), i ≠ j → p (Matrix.transvection i j c)) → (∀ D : ι → R, (∀ i, IsUnit (D i)) → p (Matrix.diagonal D)) → (∀ A B, IsUnit A.det → IsUnit B.det → p A → p B → p (A * B)) → ∀ A : Matrix ι ι R, IsUnit A.det → p A := by
  first | exact @GlobalTheory.CompanionTheory.Adelic.StableRangeOne.matrix_induction | exact GlobalTheory.CompanionTheory.Adelic.StableRangeOne.matrix_induction | (intros; apply GlobalTheory.CompanionTheory.Adelic.StableRangeOne.matrix_induction <;> assumption)
