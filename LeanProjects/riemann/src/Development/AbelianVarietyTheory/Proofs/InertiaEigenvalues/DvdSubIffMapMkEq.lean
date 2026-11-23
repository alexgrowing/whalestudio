import Mathlib

universe u_1 u_2 u_3

namespace GlobalTheory.DvdSubMapMk

theorem dvd_sub_iff_map_mk_eq {R : Type u_1} [inst : CommRing R] {p : Type u_2} {q : Type u_3}
    (a : R) (A B : Matrix p q R) :
    (∀ (i : p) (j : q), a ∣ (A - B) i j) ↔
      Matrix.map A (⇑(Ideal.Quotient.mk (Ideal.span {a})) : R → R ⧸ Ideal.span {a}) =
        Matrix.map B (⇑(Ideal.Quotient.mk (Ideal.span {a})) : R → R ⧸ Ideal.span {a}) := by
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Matrix.map_apply, Matrix.map_apply, Ideal.Quotient.eq, Ideal.mem_span_singleton,
    Matrix.sub_apply]

end GlobalTheory.DvdSubMapMk
