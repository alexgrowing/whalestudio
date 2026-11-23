import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.PairingOne

section Alg
variable {k : Type*} [Field k] {m : Type*} [Fintype m] [DecidableEq m]

def rowMat (o j : m) (l y : m → k) : Matrix m m k := fun r c =>
  if r = o then l c else (if Equiv.swap o j r = c then 1 else 0) - y (Equiv.swap o j r) * l c

def colMat (o j : m) (l y : m → k) : Matrix m m k := fun c r =>
  if r = o then y c else
    (if Equiv.swap o j r = c then 1 else 0) - (if j = c then 1 else 0) * (l (Equiv.swap o j r) / l j)

end Alg

variable {k : Type*} [Field k] [ValuativeRel k] {m : Type*} [Fintype m] [DecidableEq m]

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isCompact_bounded (t : ValueGroupWithZero k) :
    IsCompact {w : GL m k | (∀ a b, valuation k (w.val a b) ≤ t) ∧ ∀ a b, valuation k ((w⁻¹).val a b) ≤ t} := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hK : IsCompact {A : Matrix m m k | ∀ i j, valuation k (A i j) ≤ t} := by
    have h : IsCompact (Set.pi Set.univ fun _ : m => Set.pi Set.univ fun _ : m => {x : k | valuation k x ≤ t}) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k t
    have e : {A : Matrix m m k | ∀ i j, valuation k (A i j) ≤ t} =
        (Set.pi Set.univ fun _ : m => Set.pi Set.univ fun _ : m => {x : k | valuation k x ≤ t}) :=
      Set.ext fun x => ⟨fun hx i _ j _ => hx i j, fun hx i j => hx i trivial j trivial⟩
    rw [e]; exact h
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix m m k)).isCompact_preimage
    (hK.prod (hK.image MulOpposite.continuous_op))
  convert h using 1
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply,
    Set.mem_prod, (MulOpposite.op_injective).mem_set_image]

end GlobalTheory.PairingOne
