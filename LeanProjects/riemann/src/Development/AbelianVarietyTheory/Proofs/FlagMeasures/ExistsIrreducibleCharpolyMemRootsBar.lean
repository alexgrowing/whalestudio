import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm

theorem exists_irreducible_charpoly_mem_rootsBar (g : ℕ) [Fact g.Prime] (d : ℕ)
    (z : Formalism.CyclotomicNorms.Fbar g) (hz : z ≠ 0) (hd : (minpoly (ZMod g) z).natDegree = d) :
    ∃ y : Gn g d, Irreducible (y : Mt g d).charpoly ∧
      z ∈ Formalism.CyclotomicNorms.rootsBar (y : Mt g d).charpoly := by
  subst hd
  have hi : IsIntegral (ZMod g) z := Algebra.IsIntegral.isIntegral z
  let pb := IntermediateField.adjoin.powerBasis hi
  let M : Mt g (minpoly (ZMod g) z).natDegree := Algebra.leftMulMatrix pb.basis pb.gen
  have hM : M.charpoly = minpoly (ZMod g) z := by
    have h := charpoly_leftMulMatrix pb
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen] at h
    exact h
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_eq_sign_charpoly_coeff, hM]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (minpoly.coeff_zero_ne_zero hi hz)
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet, ?_, ?_⟩
  · change Irreducible M.charpoly
    rw [hM]
    exact minpoly.irreducible hi
  · change z ∈ Formalism.CyclotomicNorms.rootsBar M.charpoly
    rw [hM, Formalism.CyclotomicNorms.rootsBar, mem_roots_map (minpoly.ne_zero hi), ← aeval_def]
    exact minpoly.aeval _ _

end GlobalTheory.GLm
