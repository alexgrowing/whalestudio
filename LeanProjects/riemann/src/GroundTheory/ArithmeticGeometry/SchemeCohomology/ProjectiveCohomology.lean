import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjCechCompute
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjTwistLeray
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite MvPolynomial

universe w' u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjSpace

variable {A : Type u} [CommRing A] {n : ℕ}
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology (projectiveSpace A n).toTopCat) AddCommGrpCat.{u})]

def HZeroEquiv (k : ℕ) :
    Sheaf.H.{w'} (modulesAb (twistingSheaf (grading A n) k)) 0 ≃+
      homogeneousSubmodule (Fin (n + 1)) A k :=
  (cechHZeroEquivH (modulesAb (twistingSheaf (grading A n) k)) (cover A n)
    iSup_stdOpen).symm.trans (cechHZeroEquiv' k)

theorem nonempty_HTop_equiv (k : ℤ) (hn : 0 < n) :
    Nonempty (Sheaf.H.{w'} (modulesAb (twistingSheaf (grading A n) k)) n ≃+ (NegMon n k →₀ A)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨e⟩ := nonempty_cechH_equiv_H (A := A) (n := m + 1) k (m + 1)
  exact ⟨e.symm.trans (cechHTopEquiv k m)⟩

theorem subsingleton_H (k : ℤ) {q : ℕ} (hq0 : 0 < q) (hqn : q ≠ n) :
    Subsingleton (Sheaf.H.{w'} (modulesAb (twistingSheaf (grading A n) k)) q) := by
  obtain ⟨e⟩ := nonempty_cechH_equiv_H (A := A) (n := n) k q
  have : Subsingleton (cechH (twistAb A n k) (cover A n) q) := by
    rcases Nat.lt_or_gt_of_ne hqn with h | h
    · exact subsingleton_cechH_of_lt hq0 h
    · exact subsingleton_cechH_of_gt h
  exact e.symm.toEquiv.subsingleton

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
