import Formalism.PieriBlockIdeals.PieriColumnMinors.LrbPiSingleCast
import Formalism.PieriBlockIdeals.PieriColumnMinors.LrcFockZeroRight
import Formalism.PieriBlockIdeals.PieriColumnMinors.FsDivMem
import Formalism.PieriBlockIdeals.PieriColumnMinors.LowerTriangularIntegral
import Formalism.PieriBlockIdeals.PieriColumnMinors.HighestWeightMemWZero

open MvPolynomial

noncomputable section

namespace Formalism.CohomologicalDescent.LR

open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

def MV (p q w : ℕ) (lam2 : Fin q → ℕ) : AddSubgroup (VQ p q w lam2) :=
  ((weyl ℤ (p + q) (p + q) le_rfl (LD.blockWt p q w lam2)).map (intQ (p + q) (p + q))).toAddSubgroup.comap
    (dualWeyl ℚ (p + q) (p + q) (LD.blockWt p q w lam2)).subtype.toAddMonoidHom

theorem mem_MV (p q w : ℕ) (lam2 : Fin q → ℕ) (v : VQ p q w lam2) :
    v ∈ MV p q w lam2 ↔ (v : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) ∈
      (weyl ℤ (p + q) (p + q) le_rfl (LD.blockWt p q w lam2)).map (intQ (p + q) (p + q)) := Iff.rfl

def LevZ (p q w : ℕ) (lam2 : Fin q → ℕ) : Submodule ℤ (MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) :=
  Submodule.span ℤ (Set.range fun ω : List (Fin q × Fin q × ℕ) =>
    applyWord ℚ (liftWord p ω) (hw ℚ le_rfl (LD.blockWt p q w lam2)))

def MW (p q w : ℕ) (lam2 : Fin q → ℕ) : AddSubgroup (rationalBlockModuleSetting p q w lam2).W :=
  (LevZ p q w lam2).toAddSubgroup.comap
    (((dualWeyl ℚ (p + q) (p + q) (LD.blockWt p q w lam2)).subtype.comp
      (rationalBlockModuleSetting p q w lam2).W.subtype).toAddMonoidHom)

theorem mem_MW (p q w : ℕ) (lam2 : Fin q → ℕ) (u : (rationalBlockModuleSetting p q w lam2).W) :
    u ∈ MW p q w lam2 ↔ (((u : VQ p q w lam2)) : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) ∈ LevZ p q w lam2 :=
  Iff.rfl

def DelLR (l : ℕ) (hl : l.Prime) (p q w : ℕ) (lam2 : Fin q → ℕ) : Submodule (Zl l) (rationalBlockModuleSetting p q w lam2).W :=
  locSpan l hl (MW p q w lam2)

def xiOf {p q : ℕ} (ξ : Fin (p + q) → ℤ) : (Fin p ⊕ Fin q → ℤ) →+ ℤ where
  toFun κ := ∑ a, ξ (idx p q a) * κ a
  map_zero' := by simp
  map_add' κ κ' := by simp [mul_add, Finset.sum_add_distrib]

def lamOf (p q w : ℕ) (lam2 : Fin q → ℕ) : Fin p ⊕ Fin q → ℤ := fun a => (LD.blockWt p q w lam2 (idx p q a) : ℤ)

theorem sum_idx {p q : ℕ} (f : Fin (p + q) → ℤ) : ∑ a : Fin p ⊕ Fin q, f (idx p q a) = ∑ a, f a := by
  refine Fintype.sum_equiv finSumFinEquiv _ _ fun a => ?_
  cases a <;> rfl

theorem xiOf_depth2 {p q : ℕ} (ξ : Fin (p + q) → ℤ) (lam μ : Fin (p + q) → ℕ) :
    xiOf ξ ((fun a => (lam (idx p q a) : ℤ)) - fun a => (μ (idx p q a) : ℤ)) = LD.depth2 ξ lam μ := by
  show ∑ a, ξ (idx p q a) * (((fun a => (lam (idx p q a) : ℤ)) - fun a => (μ (idx p q a) : ℤ)) a) = _
  simp only [Pi.sub_apply]
  exact sum_idx (fun a => ξ a * ((lam a : ℤ) - (μ a : ℤ)))

end Formalism.CohomologicalDescent.LR
