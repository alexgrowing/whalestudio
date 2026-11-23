import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityWittTiltAinf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityTensorAinfCoefficients
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal Matrix

namespace GlobalTheory.FrobIntO

theorem frobenius_integrality_vec_O : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] (ι : Type) [Fintype ι] [DecidableEq ι] (Y : Matrix ι ι (OA l O)) (w : ι → OA l O) (z : ι → OW l O), (fun i => frobOW l O (z i)) = (Y.map (inclO l O)) *ᵥ z + (fun i => inclO l O (w i)) → ∀ i, z i ∈ (inclO l O).range := by
  intro l _ O _ _ _ _ ι _ _ Y w z h i
  classical
  have key := GlobalTheory.FrobIntegralCoeff.integrality_baseChange (R := ℤ_[l]) (O := O) (inclWA l) (frobW l)
    (fun p q _ _ Z S S' Y h => GlobalTheory.FrobInt.frobenius_integrality l p q Z S S' Y h) ι Unit
    (Matrix.of fun j (_ : Unit) => z j) Y 1 (Matrix.of fun j (_ : Unit) => w j) (by
      rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
      refine Matrix.ext fun j u => ?_
      have := congrFun h j
      simp only [Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mulVec,
        dotProduct, Fintype.sum_unique, Pi.add_apply] at this ⊢
      exact this) i ()
  exact key

end GlobalTheory.FrobIntO
