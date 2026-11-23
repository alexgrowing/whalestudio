import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsMultiHomogeneousFixFirstBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormIntExistsAndChowFormExists
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.AlgebraMapBaseMemMaximalIdealIff
import ReciprocityTheory.SemistableReduction.DetSubtypeCompAssociatedProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertDegreeEqSumOverComponents

open MvPolynomial GlobalTheory.ChowHt
attribute [local instance] MvPolynomial.gradedAlgebra

set_option autoImplicit false

namespace GlobalTheory.ChowSection

theorem totalDegree_of_isChowFormInt {k : Type} [Field k] {N e d : ℕ}
    {Q : Ideal (MvPolynomial (Fin N) k)} {g : MvPolynomial (Fin (e + 1) × Fin N) k}
    (h : IsChowFormInt Q e d g) : g.totalDegree = (e + 1) * d := by
  rw [((isMultiHomogeneous_iff_block.1 h.homog).isHomogeneous).totalDegree h.ne_zero]
  simp

end GlobalTheory.ChowSection
