import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCyclotomicBaseRingInvertingPrime
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cyclotomic_base_ring_inverting_prime : ∀ (n e p k : ℕ), n.Prime → p.Prime → n ≠ p → 1 ≤ e → k = n ^ e → ∃ (o : Type) (_ : CommRing o) (b : TBase o k) (em : o →+* ℂ) (j : o →+* ZP p k), ArBase em ∧ j (b.ζ : o) = zetaZP p k ∧ (∀ x, ((j x : ZP p k) : ℂ) = em x) ∧ ∀ (K : Type) [Field K] (y : Sp (DualNumber K) ⟶ Sp (ZP p k)), y = constPt y := by
  first | exact @GlobalTheory.ZM.CycBase.exists_base | exact GlobalTheory.ZM.CycBase.exists_base | (intros; apply GlobalTheory.ZM.CycBase.exists_base <;> assumption)
