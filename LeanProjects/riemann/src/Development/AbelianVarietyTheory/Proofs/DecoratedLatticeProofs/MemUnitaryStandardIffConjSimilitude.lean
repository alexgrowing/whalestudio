import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem mem_UJ_one_iff_conj_similitude :
    ∀ (R : Type) [CommRing R] (σ : R →+* R), (∀ x, σ (σ x) = x) → ∀ (N : ℕ) (M y : GL (Fin N) R) (r : Rˣ), Formalism.UG.cT σ M.1 * M.1 = (r : R) • 1 → (y ∈ Formalism.UG.UJ σ (1 : Matrix (Fin N) (Fin N) R) ↔ M⁻¹ * y * M ∈ Formalism.UG.UJ σ (1 : Matrix (Fin N) (Fin N) R)) := by
  intro R _ σ _ N M y r hM
  have hAB : M.1 * (M⁻¹).1 = 1 := Units.mul_inv M
  have hBA : (M⁻¹).1 * M.1 = 1 := Units.inv_mul M
  have h1 : Formalism.UG.cT σ M.1 = (r : R) • (M⁻¹).1 := by
    calc Formalism.UG.cT σ M.1 = Formalism.UG.cT σ M.1 * M.1 * (M⁻¹).1 := by
          rw [Matrix.mul_assoc, hAB, Matrix.mul_one]
      _ = (r : R) • (M⁻¹).1 := by rw [hM, Matrix.smul_mul, Matrix.one_mul]
  have h2 : (r : R) • (Formalism.UG.cT σ (M⁻¹).1 * (M⁻¹).1) = 1 := by
    rw [← Matrix.mul_smul, ← h1, ← Formalism.UG.cT_mul, hAB, Formalism.UG.cT_one]
  have key : Formalism.UG.cT σ (M⁻¹ * y * M).1 * 1 * (M⁻¹ * y * M).1
      = (M⁻¹).1 * (Formalism.UG.cT σ y.1 * 1 * y.1) * M.1 := by
    rw [Units.val_mul, Units.val_mul, Formalism.UG.cT_mul, Formalism.UG.cT_mul, h1]
    calc (r : R) • (M⁻¹).1 * (Formalism.UG.cT σ y.1 * Formalism.UG.cT σ (M⁻¹).1) * 1 * ((M⁻¹).1 * y.1 * M.1)
        = (M⁻¹).1 * (Formalism.UG.cT σ y.1 * ((r : R) • (Formalism.UG.cT σ (M⁻¹).1 * (M⁻¹).1)) * y.1) * M.1 := by
          simp only [Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
      _ = _ := by rw [h2]
  show Formalism.UG.cT σ y.1 * 1 * y.1 = 1 ↔
    Formalism.UG.cT σ (M⁻¹ * y * M).1 * 1 * (M⁻¹ * y * M).1 = 1
  rw [key]
  constructor
  · intro h
    rw [h, Matrix.mul_one, hBA]
  · intro h
    calc Formalism.UG.cT σ y.1 * 1 * y.1
        = (M.1 * (M⁻¹).1) * (Formalism.UG.cT σ y.1 * 1 * y.1) * (M.1 * (M⁻¹).1) := by
          simp only [hAB, Matrix.one_mul, Matrix.mul_one]
      _ = M.1 * ((M⁻¹).1 * (Formalism.UG.cT σ y.1 * 1 * y.1) * M.1) * (M⁻¹).1 := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h, Matrix.mul_one, hAB]

end GlobalTheory.StdUnn
