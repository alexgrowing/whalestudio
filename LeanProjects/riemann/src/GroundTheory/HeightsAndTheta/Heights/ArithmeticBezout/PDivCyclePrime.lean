import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ}

theorem isHomogIdeal_iff_isHomogeneous (I : Ideal (MvPolynomial (Fin n) ℂ)) :
    IsHomogIdeal I ↔ I.IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) := by
  constructor
  · intro h i r hr
    have := decomposition.decompose'_apply (σ := Fin n) (R := ℂ) r i
    change (decomposition.decompose' r i : MvPolynomial (Fin n) ℂ) ∈ I
    rw [this]
    exact h r hr i
  · intro h f hf d
    exact homogeneousComponent_mem_of_mem h hf d

theorem isHomogeneous_of_mem_minimalPrimes {I P : Ideal (MvPolynomial (Fin n) ℂ)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) ℂ)) (hP : P ∈ I.minimalPrimes) :
    P.IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) := by
  have hcore : (P.homogeneousCore (homogeneousSubmodule (Fin n) ℂ)).toIdeal.IsPrime :=
    hP.1.1.homogeneousCore
  have hle : I ≤ (P.homogeneousCore (homogeneousSubmodule (Fin n) ℂ)).toIdeal :=
    hI.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ hP.1.2)
  have hcoreP := Ideal.toIdeal_homogeneousCore_le (homogeneousSubmodule (Fin n) ℂ) P
  rw [Ideal.IsHomogeneous.iff_eq]
  exact le_antisymm hcoreP (hP.2 ⟨hcore, hle⟩ hcoreP)

theorem DivCyclePrime.proof : DivCyclePrime.Statement := by
  intro n W u hW W' hW'
  have hmem : W' ∈ relComps (W ⊔ Ideal.span {linForm u}) := by
    by_contra hc
    apply Finsupp.mem_support_iff.mp hW'
    simp only [divCycle, fundCycle, Finsupp.onFinset_apply]
    exact if_neg hc
  obtain ⟨hmin, hrel⟩ := hmem
  have hlin : (linForm u : MvPolynomial (Fin n) ℂ) ∈ homogeneousSubmodule (Fin n) ℂ 1 := by
    rw [mem_homogeneousSubmodule]
    exact IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X (u j) j
  have hJ : (W ⊔ Ideal.span {linForm u}).IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) :=
    ((isHomogIdeal_iff_isHomogeneous W).mp hW.isHomog).sup
      (Ideal.homogeneous_span _ _ fun x hx => by
        rw [Set.mem_singleton_iff] at hx
        exact hx ▸ ⟨1, hlin⟩)
  exact ⟨hmin.1.1, (isHomogIdeal_iff_isHomogeneous W').mpr
    (isHomogeneous_of_mem_minimalPrimes hJ hmin), hrel⟩

end GroundTheory.Heights₂.Heights
