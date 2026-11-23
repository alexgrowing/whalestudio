import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjugateGramSymm
open GlobalTheory.CasimirOrder

namespace GlobalTheory.CasimirOrder

open Matrix

theorem casimir_mul_pos {O : Type} [Ring O] {r : ℕ} (x : Module.Basis (Fin r) ℤ O) (s : O →+ O)
    (φ : O →+ ℤ) (hs : ∀ a b, s (a * b) = s b * s a) (hss : ∀ a, s (s a) = a)
    (_hφc : ∀ a b, φ (a * b) = φ (b * a)) (hφs : ∀ a, φ (s a) = φ a)
    (hp : ∀ a, a ≠ 0 → 0 < φ (s a * a)) :
    ∀ u, u ≠ 0 → 0 < φ (s (casimir (⇑x) s φ * u) * u) := by
  intro u hu
  classical
  set A := (gram (⇑x) s φ).adjugate with hA
  set y : Fin r → O := fun i => x i * u with hy
  set H : Matrix (Fin r) (Fin r) ℝ := Matrix.of fun i j => ((form s φ (y i) (y j) : ℤ) : ℝ) with hHdef
  have key : φ (s (casimir (⇑x) s φ * u) * u) = ∑ i, ∑ j, A i j * form s φ (y j) (y i) := by
    rw [hs]
    unfold casimir
    simp only [map_sum, map_zsmul, hs, hss, Finset.mul_sum, Finset.sum_mul, mul_smul_comm,
      smul_mul_assoc, form_apply, hy, smul_eq_mul, hA]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [mul_assoc]
  have hnn : ∀ w, 0 ≤ form s φ w w := by
    intro w
    by_cases hw : w = 0
    · simp [hw]
    · exact (hp w hw).le
  have hHpsd : H.PosSemidef := GlobalTheory.gram_posSemidef_of_int_form (form s φ) (form_symm hs hss hφs) hnn y
  have hP : (A.map (Int.cast : ℤ → ℝ)).PosDef := by
    have h1 := posDef_gram x (form s φ) (form_symm hs hss hφs) (fun w hw => by simpa using hp w hw)
    have e : A.map (Int.cast : ℤ → ℝ) = ((Matrix.of fun i j : Fin r => form s φ (x i) (x j)).map (Int.cast : ℤ → ℝ)).adjugate := by
      rw [hA, gram_eq]
      exact (RingHom.map_adjugate (Int.castRingHom ℝ) (Matrix.of fun i j : Fin r => form s φ (x i) (x j)))
    rw [e]
    exact adjugate_posDef h1
  have hy0 : ∃ i, y i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hu
    calc u = (∑ i, x.repr 1 i • x i) * u := by rw [x.sum_repr, one_mul]
      _ = ∑ i, x.repr 1 i • y i := by rw [Finset.sum_mul]; simp only [hy, smul_mul_assoc]
      _ = 0 := by simp [h]
  have hH0 : H ≠ 0 := by
    obtain ⟨i, hi⟩ := hy0
    intro h
    have h3 := hp _ hi
    have h2 := congrFun (congrFun h i) i
    rw [hHdef] at h2
    simp only [of_apply, form_apply, Matrix.zero_apply, Int.cast_eq_zero] at h2
    omega
  have ht := trace_mul_pos_real hP hHpsd hH0
  have e : (A.map (Int.cast : ℤ → ℝ) * H).trace = ((∑ i, ∑ j, A i j * form s φ (y j) (y i) : ℤ) : ℝ) := by
    simp [Matrix.trace, Matrix.mul_apply, hHdef]
  rw [e] at ht
  rw [key]
  exact_mod_cast ht

end GlobalTheory.CasimirOrder
