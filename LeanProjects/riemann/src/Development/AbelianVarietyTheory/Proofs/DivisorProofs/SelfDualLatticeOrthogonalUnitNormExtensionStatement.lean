import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeOrthogonalUnitNormExtension
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjRelEquiv
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ValIrreducible
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_lattice_orthogonal_unit_norm_extension : ∀ (K : GlobalTheory.UnitLemma.UQ) (V : Type) [AddCommGroup V] [Module K.E V] [Module K.O V] [IsScalarTower K.O K.E V]
    [FiniteDimensional K.E V] (h : V → V → K.E), (∀ y y' z, h (y + y') z = h y z + h y' z) →
    (∀ (a : K.E) y z, h (a • y) z = a * h y z) → (∀ y z, h z y = K.c (h y z)) →
    ∀ L : Submodule K.O V, L.FG → Submodule.span K.E (L : Set V) = ⊤ →
    (∀ y, y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap K.O K.E).range) →
    ∀ (k : ℕ) (f : Fin k → V), (∀ i, f i ∈ L) → (∀ i j, i ≠ j → h (f i) (f j) = 0) →
    (∀ i, ∃ t : K.O, IsUnit t ∧ h (f i) (f i) = algebraMap K.O K.E t) → k < Module.finrank K.E V →
    ∃ y ∈ L, (∀ i, h y (f i) = 0) ∧ ∃ t : K.O, IsUnit t ∧ h y y = algebraMap K.O K.E t := by
  first | exact @GlobalTheory.selfDual_orthogonal_unit_step | exact GlobalTheory.selfDual_orthogonal_unit_step | (intros; apply GlobalTheory.selfDual_orthogonal_unit_step <;> assumption)
