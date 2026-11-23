import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {ι : Type} {n : ι → ℕ}

def ratioField (x : Cone n (AlgebraicClosure ℚ)) : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  IntermediateField.adjoin ℚ
    (Set.range fun p : (k : ι) × Fin (n k + 1) × Fin (n k + 1) ↦ x p.1 p.2.1 / x p.1 p.2.2)

theorem ratioField_le_coordField (x : Cone n (AlgebraicClosure ℚ)) :
    ratioField x ≤ coordField x := by
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro _ ⟨p, rfl⟩
  exact div_mem (IntermediateField.subset_adjoin ℚ _ ⟨⟨p.1, p.2.1⟩, rfl⟩)
    (IntermediateField.subset_adjoin ℚ _ ⟨⟨p.1, p.2.2⟩, rfl⟩)

theorem div_mem_ratioField (x : Cone n (AlgebraicClosure ℚ)) (k : ι) (i j : Fin (n k + 1)) :
    x k i / x k j ∈ ratioField x :=
  IntermediateField.subset_adjoin ℚ _ ⟨⟨k, i, j⟩, rfl⟩

variable [Fintype ι]

instance (x : Cone n (AlgebraicClosure ℚ)) : FiniteDimensional ℚ (ratioField x) :=
  IntermediateField.finiteDimensional_adjoin fun y _ ↦ isIntegral_algebraicClosure_rat y

instance (x : Cone n (AlgebraicClosure ℚ)) : NumberField (ratioField x) := {}

def orbitCenter (x : Cone n (AlgebraicClosure ℚ)) (v : FinitePlace (coordField x)) :
    Ideal (MvPolynomial (Coord n) ℤ) :=
  Ideal.span {F | ∃ d : ι → ℕ, Geo.IsMultiHomog (ι := blockIdx n) F d ∧
    v (evalCone (coordVec x) F) < ∏ k, (⨆ i, v (coordVec x k i)) ^ d k}

variable [DecidableEq ι]

theorem X_mem_orbitCenter (x : Cone n (AlgebraicClosure ℚ)) (v : FinitePlace (coordField x))
    (k : ι) (i : Fin (n k + 1)) (hi : v (coordVec x k i) < ⨆ j, v (coordVec x k j)) :
    (X ⟨k, i⟩ : MvPolynomial (Coord n) ℤ) ∈ orbitCenter x v := by
  refine Ideal.subset_span ⟨coordDeg n ⟨k, i⟩, (geoMultiHomog_iff _ _).mpr
    (isWeightedHomogeneous_X ℤ (coordDeg n) ⟨k, i⟩), ?_⟩
  simpa [evalCone, coordDeg, Pi.single_apply, pow_ite] using hi

example : (1 / 2 : AlgebraicClosure ℚ) ∈ ratioField samplePoint := by
  convert div_mem_ratioField samplePoint () 0 1 using 1
  simp [samplePoint]

end

end GroundTheory.Heights₂.Heights
