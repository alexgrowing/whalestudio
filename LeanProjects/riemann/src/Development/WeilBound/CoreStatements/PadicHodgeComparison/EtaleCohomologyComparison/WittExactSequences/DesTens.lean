import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ResKill
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.PowersGood

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison.CH

universe w v u v' u' v'' u''

namespace CrystallineSemistableComparison.D

variable (l : ℕ) [Fact l.Prime]

theorem rt_pow (k N : ℕ) : rt l (k + N) ^ (l ^ N) = rt l k := by
  induction N with
  | zero => rw [pow_zero, pow_one, add_zero]
  | succ N ih => rw [pow_succ', pow_mul, ← add_assoc, (isRt_rt l).1 (k + N), ih]

theorem rt_ideal (N : ℕ) : Ideal.span (Set.range (rt l)) ≤
    Ideal.span ((fun a => a ^ N) '' (Ideal.span (Set.range (rt l)) : Set (Ob l))) := by
  rw [Ideal.span_le]
  rintro _ ⟨k, rfl⟩
  have hN : N ≤ l ^ N := (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le
  rw [← rt_pow l k N, ← Nat.sub_add_cancel hN, pow_add]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨rt l (k + N), Ideal.subset_span ⟨k + N, rfl⟩, rfl⟩)

theorem des_tens (h : ObFacts l) (N : Type) [AddCommGroup N] [Module (Ob l) N] (M : ℕ) (hN : ∀ x : N, pFlat l ^ M • x = 0) (k : ℕ) :
    Des (toPf l ⋙ tensF l (Ob l) N) (rt l k) := by
  have := (toPf_full l).1
  have := (toPf_full l).2
  have hdes : DesJ (testι l ⋙ toPf l) (tensF l (Ob l) N) (rt l k) := fun A =>
    CrystallineSemistableComparison.P.induct (testι l ⋙ toPf l) (tensF l (Ob l) N) _ (rt_ideal l) (fun A => powers_good l h N M hN A) A _
      (Ideal.subset_span ⟨k, rfl⟩)
  exact des_ff (testι l) (toPf l) _ _ hdes

end CrystallineSemistableComparison.D
