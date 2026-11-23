import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.QhtUnip

namespace GlobalTheory.QhtUnip

theorem heis_mul : ∀ (R : Type) [CommRing R] (m : ℕ) (a w a' w' : Fin m → R) (α α' : R),
    Heisenberg₂ a w α * Heisenberg₂ a' w' α' = Heisenberg₂ (a + a') (w + w') (α + α' + ∑ k, a k * w' k) := by
  intro R _ m a w a' w' α α'
  ext ((i | i) | i) ((j | j) | j) <;>
    simp [Heisenberg₂, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.fromBlocks, Fin.fin_one_eq_zero] <;> ring

end GlobalTheory.QhtUnip
