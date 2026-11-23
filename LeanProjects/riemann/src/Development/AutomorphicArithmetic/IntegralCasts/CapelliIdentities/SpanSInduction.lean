import Mathlib

noncomputable def UpperTheory.Reformulated.B.Qe24.spanS.{u_1, u_2} :
    {K : Type u_1} →
      {V : Type u_2} →
        [inst : Field K] →
          [inst_1 : AddCommGroup V] →
            [inst_2 : _root_.Module K V] → (S : Subring K) → {n : ℕ} → (Fin n → V) → Submodule (↥S) V :=
    fun {K : Type u_1} {V : Type u_2} [Field K] [AddCommGroup V] [_root_.Module K V] (S : Subring K) {n : ℕ}
        (x : Fin n → V) ↦
      Submodule.span (↥S) (Set.range x)

theorem UpperTheory.Reformulated.B.Qe24.spanS_induction.{u_1, u_2} :
    ∀ {K : Type u_1} {V : Type u_2} [inst : Field K] [StarRing K] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module K V]
      {S : Subring K} {n : ℕ} {x : Fin n → V} {p : V → Prop},
      p (0 : V) →
        (∀ (a b : V), p a → p b → p (a + b)) →
          (∀ c ∈ S, ∀ (a : V), p a → p (c • a)) → (∀ (i : Fin n), p (x i)) → ∀ v ∈ UpperTheory.Reformulated.B.Qe24.spanS S x, p v := by
  intro K V _ _ _ _ S n x p h0 hadd hsmul hx v hv
  unfold UpperTheory.Reformulated.B.Qe24.spanS at hv
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact hx i
  | zero => exact h0
  | add a b _ _ ha hb => exact hadd a b ha hb
  | smul c a _ ha => exact hsmul c.1 c.2 a ha
