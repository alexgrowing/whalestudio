import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf

theorem gramQ_unitri : ∀ (D : D7) (W : HSp D) (ρ : ℕ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), IsBase W x₀ → ∀ u : Matrix (Fin ρ) (Fin ρ) D.host.E, (∀ i, u i i = 1) → (∀ i k, k < i → u i k = 0) → uᴴ * gramQ W x₀ * u = gramQ W x₀ := by
  intro D W ρ x₀ hb u hd hl
  have htri : (rat u : Mx D ρ ρ).BlockTriangular id := fun i j (h : j < i) => by
    show incA D (u i j) = 0
    rw [hl i j h, map_zero]
  have hdiag : ∀ i, (rat u : Mx D ρ ρ) i i = 1 := fun i => by
    show incA D (u i i) = 1
    rw [hd i, map_one]
  have hu : IsUnit (rat u : Mx D ρ ρ) := (Matrix.isUnit_iff_isUnit_det _).2 (by
    rw [Matrix.det_of_upperTriangular htri]; simp only [hdiag, Finset.prod_const_one]; exact isUnit_one)
  have hmem : hu.unit ∈ UX D ρ := fun i j => ⟨fun h => htri h, hdiag i⟩
  have h := hb.2 _ hmem
  rw [IsUnit.unit_spec] at h
  apply rat_injective
  rw [rat_mul, rat_mul, rat_conjTranspose, Matrix.mul_assoc]
  exact h

end GlobalTheory.Unf

end
