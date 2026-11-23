import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

namespace GlobalTheory.UnitLemma.Unr

theorem conj_matrix_det_isUnit : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), (∀ x, φ (K.c x) = K'.c (φ x)) → letI : Algebra K.E K'.E := φ.toAlgebra; ∀ w : Module.Basis (Fin d) K.E K'.E, (∀ z : K'.E, (∃ y : K'.O, algebraMap K'.O K'.E y = z) ↔ ∀ k, ∃ a : K.O, algebraMap K.O K.E a = w.repr z k) → ∃ u : K.O, IsUnit u ∧ algebraMap K.O K.E u = (Matrix.of fun m l => w.repr (K'.c (w l)) m).det := by
  intro K K' d φ hφ
  letI : Algebra K.E K'.E := φ.toAlgebra
  intro w hw
  set C : Matrix (Fin d) (Fin d) K.E := Matrix.of fun m l => w.repr (K'.c (w l)) m with hC
  have hsm : ∀ (e : K.E) (x : K'.E), e • x = φ e * x := fun e x => rfl
  have hint : ∀ m l, ∃ a : K.O, algebraMap K.O K.E a = C m l := by
    intro m l
    have h1 : ∃ y : K'.O, algebraMap K'.O K'.E y = w l := by
      rw [hw]
      intro k
      rw [w.repr_self]
      by_cases h : l = k
      · subst h; exact ⟨1, by simp⟩
      · exact ⟨0, by simp [Finsupp.single_apply, h]⟩
    obtain ⟨y, hy⟩ := h1
    obtain ⟨y', hy'⟩ := K'.c_int y
    have h2 : ∃ y : K'.O, algebraMap K'.O K'.E y = K'.c (w l) := ⟨y', by rw [← hy', hy]⟩
    exact (hw _).1 h2 m
  choose A hA using hint
  have hrep : ∀ (x : K'.E) (n : Fin d), w.repr (K'.c x) n = ∑ m, K.c (w.repr x m) * C n m := by
    intro x n
    have hx : K'.c x = ∑ m, K.c (w.repr x m) • K'.c (w m) := by
      conv_lhs => rw [← w.sum_repr x]
      rw [map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hsm, hsm, map_mul, ← hφ]
    rw [hx, map_sum, Finsupp.finset_sum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    rfl
  have hCC : C * (K.c : K.E →+* K.E).mapMatrix C = 1 := by
    ext n l
    have h := hrep (K'.c (w l)) n
    rw [K'.c_c, w.repr_self, Finsupp.single_apply] at h
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.coe_coe]
    rw [eq_comm]
    convert h using 1
    · exact if_congr eq_comm rfl rfl
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_comm]
    rfl
  have hdet : C.det * K.c C.det = 1 := by
    have h := congrArg Matrix.det hCC
    rw [Matrix.det_mul, Matrix.det_one, ← RingHom.map_det] at h
    exact h
  have hdetA : algebraMap K.O K.E (Matrix.of A).det = C.det := by
    rw [RingHom.map_det]
    congr 1
    ext m l
    simp [hA]
  refine ⟨(Matrix.of A).det, ?_, hdetA⟩
  obtain ⟨β, hβ⟩ := K.c_int (Matrix.of A).det
  apply IsUnit.of_mul_eq_one β
  apply IsFractionRing.injective K.O K.E
  rw [map_mul, ← hβ, hdetA, hdet, map_one]

end GlobalTheory.UnitLemma.Unr
