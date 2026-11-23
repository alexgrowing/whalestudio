import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockChainSum
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockTop
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChangeOfLattice
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.RelIndexNeZeroOfMulMem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

set_option linter.unusedSectionVars false

namespace ChangeOfLatticeNested

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem exists_mul_mem_sec_one (x : Ix κ → Ω) (B : Matrix (Ix κ) (Ix κ) ℚ) :
    ∃ M : ℕ, 0 < M ∧ ∀ s ∈ sec ℤ (matAct B x) 1, (M : Ω) * s ∈ sec ℤ x 1 := by
  obtain ⟨d, hd0, hdB⟩ := ChangeOfLattice.exists_clear_den B
  refine ⟨d, Nat.pos_of_ne_zero hd0, fun s hs => ?_⟩
  rw [sec_one'] at hs ⊢
  induction hs using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨i, rfl⟩ := hs
    have e : (d : Ω) * matAct B x i = matAct ((d : ℚ) • B) x i := by
      simp only [matAct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
      push_cast
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    exact ChangeOfLattice.matAct_mem_span (fun i j => by simpa [Matrix.smul_apply] using hdB i j) x i
  | zero => simp
  | add a b _ _ ha hb =>
    rw [mul_add]
    exact add_mem ha hb
  | smul k a _ ha =>
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ k ha

theorem latLogIndex_eq_sum (x : Ix κ → Ω) (B : Matrix (Ix κ) (Ix κ) ℚ)
    (hle : Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x))) (n : ℕ) :
    latLogIndex x (matAct B x) n = ∑ j ∈ Finset.range n, twoBlockStep x (matAct B x) (n - j - 1) j := by
  have h1 : sec ℤ x 1 ≤ sec ℤ (matAct B x) 1 := by
    rw [sec_one', sec_one']
    exact hle
  have one : (sec ℤ (matAct B x) n).toAddSubgroup.relIndex (sec ℤ x n).toAddSubgroup = 1 :=
    AddSubgroup.relIndex_eq_one.2 fun _ h => ChangeOfLattice.sec_mono hle n h
  unfold latLogIndex
  rw [one, Nat.cast_one, Real.log_one, sub_zero, log_relIndex_eq_sum x _ h1 (exists_mul_mem_sec_one x B) n]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  unfold twoBlockStep
  rw [show n - j - 1 + 1 = n - j by omega]

end ChangeOfLatticeNested

theorem ChangeOfLatticeNested.proof (hS : TwoBlockChainSum.Statement) (hT : TwoBlockTop.Statement) :
    ChangeOfLatticeNested.Statement := by
  intro D Ω _ _ κ _ I x B m m' hI hX hx hB hm hm' hsp
  obtain ⟨e0, e1⟩ := hT D Ω κ I x B m m' hI hX hx hB hm hm'
  have h := hS D Ω κ I x B m m' hI hX hx hB hm hm' hsp
  rw [e0, e1] at h
  refine h.congr_left fun n => ?_
  rw [ChangeOfLatticeNested.latLogIndex_eq_sum x B hsp n]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
