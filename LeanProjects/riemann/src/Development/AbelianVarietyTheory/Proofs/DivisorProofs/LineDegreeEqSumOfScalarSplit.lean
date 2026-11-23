import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistAtOfNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldFiniteSupportSumOrderEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleAdelicMatrixFamilyOrdersFiniteStatement

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef Polynomial

namespace GlobalTheory.Nef

theorem degLine_eq_sum_of_split : ∀ (k E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field E] [Algebra k E], IsFF k E → ∀ (m n : ℕ) (G : Place k E → Matrix (Fin 2) (Fin 2) E), admitted G → ∀ (S : Place k E → Matrix (Fin n) (Fin n) E) (q : Fin n → E) (c : E) (w : Fin m → Fin 2 → E), c ≠ 0 → (∀ j, w j ≠ 0) → (∀ P, ordVec P ((S P).mulVec q) = ord P c + ∑ j, ordVec P ((G P).mulVec (w j))) → degLine S q = ∑ j, degLine G (w j) := by
  intro k E _ _ _ _ _ hE m n G hG S q c w hc hw hpt
  obtain ⟨hcfin, hcsum⟩ := GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k E hE c hc
  have hcs : (Function.support fun P : Place k E => ord P c).Finite :=
    hcfin.subset fun P hP => by
      intro h1
      apply hP
      simp [ord, h1]
  have hjs : ∀ j, (Function.support fun P : Place k E => ordVec P ((G P).mulVec (w j))).Finite := fun j =>
    ((GlobalTheory.T.admissibleAdelicMatrixFamily_orders_finite k E hE 2 G hG).2 (w j) (hw j)).1.subset fun P hP => by
      intro h1
      apply hP
      show ordVec P ((G P).mulVec (w j)) = 0
      rw [ordVec, h1]
      simp
  have hss : (Function.support fun P : Place k E => ∑ j, ordVec P ((G P).mulVec (w j))).Finite :=
    (Set.finite_iUnion fun j => hjs j).subset fun P hP => by
      obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hP
      exact Set.mem_iUnion.2 ⟨j, hj⟩
  unfold degLine
  rw [finsum_congr hpt, finsum_add_distrib hcs hss, hcsum, zero_add]
  exact finsum_sum_comm _ _ fun j _ => hjs j

end GlobalTheory.Nef
