import Formalism.SharpRestriction.GrowthBounds.RootWeights.CrRootMem
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FirstStatementB

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def cr_C (E : GLOps n K V) : Module.End K V := ∑ a : Fin n, ∑ b : Fin n, E a b * E b a

theorem cr_C_comm (E : GLOps n K V) (hR : SatisfiesGLRelations E) (c d : Fin n) : cr_C E * E c d = E c d * cr_C E := by
  classical
  have key : ∀ a b, E a b * E b a * E c d - E c d * (E a b * E b a) =
      E a b * ((if a = c then E b d else 0) - (if d = b then E c a else 0)) +
        ((if b = c then E a d else 0) - (if d = a then E c b else 0)) * E b a := by
    intro a b
    rw [← hR b a c d, ← hR a b c d]; noncomm_ring
  have S1 : ∑ a : Fin n, ∑ b : Fin n, E a b * (if a = c then E b d else 0) = ∑ b, E c b * E b d := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [mul_ite]
  have S2 : ∑ a : Fin n, ∑ b : Fin n, E a b * (if d = b then E c a else 0) = ∑ a, E a d * E c a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [mul_ite]
  have S3 : ∑ a : Fin n, ∑ b : Fin n, (if b = c then E a d else 0) * E b a = ∑ a, E a d * E c a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [ite_mul]
  have S4 : ∑ a : Fin n, ∑ b : Fin n, (if d = a then E c b else 0) * E b a = ∑ b, E c b * E b d := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [ite_mul]
  rw [← sub_eq_zero, cr_C, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have : ∀ a : Fin n, (∑ b : Fin n, E a b * E b a) * E c d - E c d * ∑ b : Fin n, E a b * E b a =
      ∑ b : Fin n, (E a b * ((if a = c then E b d else 0) - (if d = b then E c a else 0)) +
        ((if b = c then E a d else 0) - (if d = a then E c b else 0)) * E b a) := by
    intro a
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => key a b
  rw [Finset.sum_congr rfl fun a _ => this a]
  simp only [mul_sub, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [S1, S2, S3, S4]
  abel

theorem cr_C_comm_apply (E : GLOps n K V) (hR : SatisfiesGLRelations E) (c d : Fin n) (x : V) :
    cr_C E (E c d x) = E c d (cr_C E x) := by
  have := congrArg (fun f : Module.End K V => f x) (cr_C_comm E hR c d)
  simpa using this

theorem cr_sym {M : Type*} [AddCommMonoid M] (F : Fin n → Fin n → M) :
    ∑ a, ∑ b, F a b = ∑ a, F a a + ∑ a, ∑ b, if a < b then F a b + F b a else 0 :=
  _root_.UpperTheory.Reformulated.B.DoubleSumDiagonalOffDiagonal.main F

theorem cr_C_wt (E : GLOps n K V) (hR : SatisfiesGLRelations E) (mu : Fin n → ℤ) (x : V) (hx : x ∈ weightSp E mu) :
    cr_C E x = ((cr_c mu : ℤ) : K) • x + (2 : K) • ∑ a : Fin n, ∑ b : Fin n, if a < b then E b a (E a b x) else 0 := by
  classical
  have hx' := (v2rep_mem_weightSp E mu x).1 hx
  have e0 : cr_C E x = ∑ a : Fin n, ∑ b : Fin n, E a b (E b a x) := by
    simp [cr_C, LinearMap.sum_apply]
  have e1 : ∀ a, E a a (E a a x) = ((mu a : K) ^ 2) • x := by
    intro a
    rw [hx' a, map_smul, hx' a, smul_smul, sq]
  have e2 : ∀ a b : Fin n, E a b (E b a x) + E b a (E a b x) =
      (2 : K) • E b a (E a b x) + ((mu a : K) - (mu b : K)) • x := by
    intro a b
    rw [v2rep_comm E hR a b b a x]
    simp only [if_true, hx' a, hx' b, sub_smul, two_smul]
    abel
  rw [e0, cr_sym, Finset.sum_congr rfl fun a _ => e1 a]
  have e3 : ∀ a b : Fin n, (if a < b then E a b (E b a x) + E b a (E a b x) else 0) =
      (2 : K) • (if a < b then E b a (E a b x) else 0) + (if a < b then ((mu a : K) - (mu b : K)) else 0) • x := by
    intro a b
    split_ifs
    · exact e2 a b
    · simp
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => e3 a b]
  simp only [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.sum_smul]
  have e4 : ((cr_c mu : ℤ) : K) = ∑ a, (mu a : K) ^ 2 + ∑ a : Fin n, ∑ b : Fin n,
      (if a < b then ((mu a : K) - (mu b : K)) else 0) := by
    simp only [cr_c, cr_h]
    push_cast
    rfl
  rw [e4, add_smul]
  abel

theorem cr_C_hwv (E : GLOps n K V) (hR : SatisfiesGLRelations E) (mu : Fin n → ℤ) (v : V) (hv : IsHWV E mu v) :
    cr_C E v = ((cr_c mu : ℤ) : K) • v := by
  rw [cr_C_wt E hR mu v hv.2.1]
  have : ∑ a : Fin n, ∑ b : Fin n, (if a < b then E b a (E a b v) else 0) = 0 := by
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    split_ifs with h
    · rw [hv.2.2 a b h, map_zero]
    · rfl
  rw [this, smul_zero, add_zero]

theorem cr_C_stable (E : GLOps n K V) (W : Submodule K V) (hW : IsStableUnderOperators E W) (x : V) (hx : x ∈ W) :
    cr_C E x ∈ W := by
  simp only [cr_C, LinearMap.sum_apply, Module.End.mul_apply]
  exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => hW a b _ (hW b a _ hx)

theorem cr_C_weightSp (E : GLOps n K V) (hR : SatisfiesGLRelations E) (mu : Fin n → ℤ) (x : V) (hx : x ∈ weightSp E mu) :
    cr_C E x ∈ weightSp E mu := by
  rw [v2rep_mem_weightSp] at hx ⊢
  intro a
  rw [← cr_C_comm_apply E hR, hx a, map_smul]

end Formalism.MainNotions.G.GLWeightTheory
