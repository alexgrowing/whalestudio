import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock

open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.LinSchur

theorem addChar_neg_eq_one {A : Type} [AddGroup A] (ψ : AddChar A ℂ) {x : A} (h : ψ x = 1) : ψ (-x) = 1 := by
  have e := AddChar.map_add_eq_mul ψ (-x) x
  rw [neg_add_cancel, AddChar.map_zero_eq_one, h, mul_one] at e
  exact e.symm

variable {k : Type} [Field k] [ValuativeRel k]

def latt (ψ0 : AddChar k ℂ) (n d : ℕ) (s : k) : AddSubgroup (Matrix (Fin n) (Fin d) k) where
  carrier := {Y | ∀ i j, ∀ o : k, ValuativeRel.valuation k o ≤ 1 → ψ0 (o * (s * Y i j)) = 1}
  add_mem' := by
    intro a b ha hb i j o ho
    simp only [Set.mem_ofPred_eq, Matrix.add_apply, mul_add, AddChar.map_add_eq_mul] at *
    rw [ha i j o ho, hb i j o ho, one_mul]
  zero_mem' := by
    intro i j o _
    simp
  neg_mem' := by
    intro a ha i j o ho
    simp only [Set.mem_ofPred_eq, Matrix.neg_apply, mul_neg] at *
    exact addChar_neg_eq_one ψ0 (ha i j o ho)

theorem mem_latt {ψ0 : AddChar k ℂ} {n d : ℕ} {s : k} {Y : Matrix (Fin n) (Fin d) k} :
    Y ∈ latt ψ0 n d s ↔ ∀ i j, ∀ o : k, ValuativeRel.valuation k o ≤ 1 → ψ0 (o * (s * Y i j)) = 1 := Iff.rfl

open Classical in

def cind {X : Type} [AddGroup X] (L : AddSubgroup X) (y : X) : X → ℂ := fun Y => if Y - y ∈ L then 1 else 0

end GlobalTheory.LinSchur
