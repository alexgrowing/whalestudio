import Mathlib

namespace UpperTheory.Reformulated.B.P6.r26a

open scoped HSub SubNegMonoid AddGroup AddGroupWithOne Ring HMul Distrib OfNat Zero MulZeroClass Finset Semiring Fin Complex AddCommGroup Module Module.End

noncomputable def PositivityTheory.D.DSIC.KRel :
    {n : ℕ} → {A : Type} → [inst_h0 : Ring A] → (Fin n → Bool) → (Fin n → Fin n → A) → Prop :=
  fun {n : ℕ} {A : Type} {inst_f0 : Ring A} (ε_h1 : Fin n → Bool) (F : Fin n → Fin n → A) ↦ ∀ (a b c d : Fin n), ε_h1 a = ε_h1 b → ε_h1 c = ε_h1 d → F a b * F c d - F c d * F a b = (if b = c then F a d else OfNat.ofNat (nat_lit 0)) - if d = a then F c b else OfNat.ofNat (nat_lit 0)

noncomputable def Formalism.REAL.CasK.{u_1} :
    {A : Type u_1} → [inst_h0 : Ring A] → {n : ℕ} → (Fin n → Bool) → (Fin n → Fin n → A) → A :=
  fun {A : Type u_1} {inst_f1 : Ring A} {n : ℕ} (ε_h1 : Fin n → Bool) (E : Fin n → Fin n → A) ↦ ∑ a : Fin n, ∑ b : Fin n, if ε_h1 a = ε_h1 b then E a b * E b a else OfNat.ofNat (nat_lit 0)

theorem commutator_casimir_term {V : Type} [AddCommGroup V] [_root_.Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (hK : PositivityTheory.D.DSIC.KRel ε E) {c d : Fin n} (hcd : ε c = ε d)
    (a b : Fin n) :
    E c d * (if ε a = ε b then E a b * E b a else 0) - (if ε a = ε b then E a b * E b a else 0) * E c d
      = ((if ε a = ε b then (if d = a then E c b * E b a else 0) else 0)
          - (if ε a = ε b then (if a = c then E a b * E b d else 0) else 0))
        + ((if ε a = ε b then (if d = b then E a b * E c a else 0) else 0)
          - (if ε a = ε b then (if b = c then E a d * E b a else 0) else 0)) := by
  by_cases h : ε a = ε b
  · simp only [if_pos h]
    have h1 : E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0) :=
      hK a b c d h hcd
    have h2 : E b a * E c d - E c d * E b a = (if a = c then E b d else 0) - (if d = b then E c a else 0) :=
      hK b a c d h.symm hcd
    have key : E c d * (E a b * E b a) - E a b * E b a * E c d
        = -((E a b * E c d - E c d * E a b) * E b a) - E a b * (E b a * E c d - E c d * E b a) := by
      noncomm_ring
    rw [key, h1, h2]
    simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero]
    abel
  · simp only [if_neg h]
    simp

theorem double_sum_reduce_first {V : Type} [AddCommGroup V] [_root_.Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) :
    (∑ a : Fin n, ∑ b : Fin n, (if ε a = ε b then (if d = a then E c b * E b a else 0) else 0))
      = ∑ b : Fin n, (if ε d = ε b then E c b * E b d else 0) := by
  rw [Finset.sum_eq_single d]
  · apply Finset.sum_congr rfl
    intro b _
    simp
  · intro a _ had
    apply Finset.sum_eq_zero
    intro b _
    simp [Ne.symm had]
  · intro h
    exact absurd (Finset.mem_univ d) h

theorem double_sum_reduce_fourth {V : Type} [AddCommGroup V] [_root_.Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) :
    (∑ a : Fin n, ∑ b : Fin n, (if ε a = ε b then (if a = c then E a b * E b d else 0) else 0))
      = ∑ b : Fin n, (if ε c = ε b then E c b * E b d else 0) := by
  rw [Finset.sum_eq_single c]
  · apply Finset.sum_congr rfl
    intro b _
    simp
  · intro a _ hac
    apply Finset.sum_eq_zero
    intro b _
    simp [hac]
  · intro h
    exact absurd (Finset.mem_univ c) h

theorem double_sum_reduce_third {V : Type} [AddCommGroup V] [_root_.Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) :
    (∑ a : Fin n, ∑ b : Fin n, (if ε a = ε b then (if d = b then E a b * E c a else 0) else 0))
      = ∑ a : Fin n, (if ε a = ε d then E a d * E c a else 0) := by
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single d]
  · simp
  · intro b _ hbd
    simp [Ne.symm hbd]
  · intro h
    exact absurd (Finset.mem_univ d) h

theorem double_sum_reduce_second {V : Type} [AddCommGroup V] [_root_.Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) :
    (∑ a : Fin n, ∑ b : Fin n, (if ε a = ε b then (if b = c then E a d * E b a else 0) else 0))
      = ∑ a : Fin n, (if ε a = ε c then E a d * E c a else 0) := by
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single c]
  · simp
  · intro b _ hbc
    simp [hbc]
  · intro h
    exact absurd (Finset.mem_univ c) h

theorem PositivityTheory.D.LK.casK_comm :
    ∀ {n : ℕ} {ε_h0 : Fin n → Bool} {V : Type} [inst_h2 : AddCommGroup V] [inst_h3 : _root_.Module ℂ V] {E : Fin n → Fin n → Module.End ℂ V}, PositivityTheory.D.DSIC.KRel ε_h0 E → ∀ {c d : Fin n}, ε_h0 c = ε_h0 d → Commute (E c d) (Formalism.REAL.CasK ε_h0 E) := by
  intro n ε V _ _ E hK c d hcd
  show E c d * Formalism.REAL.CasK ε E = Formalism.REAL.CasK ε E * E c d
  rw [← sub_eq_zero]
  have hsum : E c d * Formalism.REAL.CasK ε E - Formalism.REAL.CasK ε E * E c d
      = ∑ a : Fin n, ∑ b : Fin n, (E c d * (if ε a = ε b then E a b * E b a else 0)
          - (if ε a = ε b then E a b * E b a else 0) * E c d) := by
    unfold Formalism.REAL.CasK
    simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]
  rw [hsum]
  simp only [commutator_casimir_term ε E hK hcd, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [double_sum_reduce_first, double_sum_reduce_fourth, double_sum_reduce_third, double_sum_reduce_second, hcd]
  simp

end UpperTheory.Reformulated.B.P6.r26a
