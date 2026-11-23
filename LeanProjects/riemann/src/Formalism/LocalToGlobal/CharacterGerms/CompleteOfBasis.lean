import Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrPl
import Lemmata.MiscLemmasH.Imports

set_option autoImplicit false

noncomputable section

open TensorProduct IsLocalRing Polynomial

namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl

section Complete

variable {Z : Type} [CommRing Z] (π : Z) {A : Type} [CommRing A] [Algebra Z A] {N : ℕ}
  (β : Module.Basis (Fin N) Z A)

theorem mem_pow_iff (n : ℕ) (x : A) :
    x ∈ ((Ideal.span {algebraMap Z A π}) ^ n • (⊤ : Submodule A A)) ↔
      ∀ i, β.repr x i ∈ ((Ideal.span {π}) ^ n • (⊤ : Submodule Z Z)) := by
  simp only [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, rfl⟩ i
    refine ⟨β.repr y i, ?_⟩
    rw [← map_pow, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
  · intro h
    choose d hd using h
    refine ⟨∑ i, d i • β i, ?_⟩
    conv_lhs => rw [← β.sum_repr x]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hd i, mul_smul, Algebra.smul_def (π ^ n), map_pow]

include β in
theorem complete_of_basis [IsAdicComplete (Ideal.span {π}) Z] :
    IsAdicComplete (Ideal.span {algebraMap Z A π}) A where
  haus' := by
    intro x hx
    have h0 : ∀ i, β.repr x i = 0 := by
      intro i
      refine IsHausdorff.haus' (I := Ideal.span {π}) _ fun n => ?_
      rw [SModEq.sub_mem, sub_zero]
      have := hx n
      rw [SModEq.sub_mem, sub_zero] at this
      exact (mem_pow_iff π β n x).1 this i
    have : β.repr x = 0 := Finsupp.ext h0
    simpa using this
  prec' := by
    intro f hf
    have h1 : ∀ i, ∃ L : Z, ∀ n, β.repr (f n) i ≡ L [SMOD ((Ideal.span {π}) ^ n • (⊤ : Submodule Z Z))] := by
      intro i
      refine IsPrecomplete.prec' (I := Ideal.span {π}) (fun n => β.repr (f n) i) ?_
      intro m n hmn
      have := hf hmn
      rw [SModEq.sub_mem] at this ⊢
      have h2 := (mem_pow_iff π β m _).1 this i
      simpa using h2
    choose L hL using h1
    refine ⟨∑ i, L i • β i, fun n => ?_⟩
    rw [SModEq.sub_mem, mem_pow_iff π β]
    intro i
    have := hL i n
    rw [SModEq.sub_mem] at this
    have e : β.repr (∑ j, L j • β j) i = L i := by
      simp [Finsupp.single_apply]
    rw [map_sub, Finsupp.sub_apply, e]
    exact this

end Complete

section Lift

variable {A : Type} [CommRing A] (I : Ideal A)

theorem lift_idem [IsAdicComplete I A] (ε : A) (h : ε * ε - ε ∈ I) : ∃ e : A, e * e = e ∧ e - ε ∈ I := by
  first | exact Bl.SecondBlockLemmaI.goal1 .. | (apply Bl.SecondBlockLemmaI.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaI.goal1 <;> assumption)

theorem idem_zero [IsHausdorff I A] {f : A} (h : f * f = f) (hf : f ∈ I) : f = 0 := by
  refine IsHausdorff.haus (I := I) ‹_› f fun n => ?_
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]
  rcases n with _ | n
  · simp
  · have he : IsIdempotentElem f := h
    rw [← he.pow_succ_eq n]
    exact Ideal.pow_mem_pow hf _

end Lift

end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
