import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceObjects
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericFibreRadicalAway
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix

noncomputable section

def universalSliceIdeal {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (d : ℕ) (q : Fin n → ℂ) :
    Ideal (MvPolynomial (Fin n) (MvPolynomial (Fin d × Fin n) ℂ)) :=
  J.map (MvPolynomial.map (C : ℂ →+* MvPolynomial (Fin d × Fin n) ℂ)) ⊔
    Ideal.span (Set.range fun i : Fin d => ∑ j, C (X (i, j)) * (X j - C (C (q j))))

theorem fibreIdeal_universalSliceIdeal {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (L : Matrix (Fin d) (Fin n) ℂ) :
    fibreIdeal (universalSliceIdeal J d q) (fun ij => L ij.1 ij.2) = sliceIdeal J L q := by
  rw [fibreIdeal, universalSliceIdeal, Ideal.map_sup, ← fibreIdeal, fibreIdeal_map_C, Ideal.map_span,
    sliceIdeal, ← Set.range_comp]
  have h : (MvPolynomial.map (eval fun ij : Fin d × Fin n => L ij.1 ij.2)) ∘
      (fun i : Fin d => ∑ j, C (X (i, j)) * (X j - C (C (q j)))) =
      fun i => ComplexSets.linPoly L i - C ((L *ᵥ q) i) := by
    funext i
    simp [ComplexSets.linPoly, Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib, map_sum]
  rw [h]

def SliceBundleRadicalAway.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ), J.IsRadical → ∀ k : Fin n,
    IsRadicalAway (universalSliceIdeal J d q) (X k - C (C (q k)))

end

end GroundTheory.Heights₂.Heights
