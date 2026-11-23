import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
open NumberField IsDedekindDomain

namespace GlobalTheory.TjCount

theorem Tj_complex_ne_zero_iff {L : Type} [Field L] (n : ℕ) (O : Subring L) (ϖ : L) (j : ℕ)
    (g : GL (Fin n) L) : Formalism.UG.Tj ℂ n O ϖ j g ≠ 0 ↔ Formalism.UG.Tj ℤ n O ϖ j g ≠ 0 := by
  unfold Formalism.UG.Tj
  rw [Set.indicator_apply_ne_zero, Set.indicator_apply_ne_zero]
  simp

theorem prod_le_pow (q n j : ℕ) (hq : 2 ≤ q) (hj : j ≤ n) :
    0 < ∏ i ∈ Finset.range j, ((q : ℤ) ^ (n - i) - 1) ∧
    ∏ i ∈ Finset.range j, ((q : ℤ) ^ (n - i) - 1) ≤ (q : ℤ) ^ (n * j) := by
  have hq1 : (1 : ℤ) < q := by exact_mod_cast (by omega : 1 < q)
  have hpos : ∀ i ∈ Finset.range j, (0 : ℤ) < (q : ℤ) ^ (n - i) - 1 := by
    intro i hi
    rw [Finset.mem_range] at hi
    have : (1 : ℤ) < (q : ℤ) ^ (n - i) := one_lt_pow₀ hq1 (by omega)
    linarith
  refine ⟨Finset.prod_pos hpos, ?_⟩
  calc ∏ i ∈ Finset.range j, ((q : ℤ) ^ (n - i) - 1)
      ≤ ∏ _i ∈ Finset.range j, (q : ℤ) ^ n := by
        apply Finset.prod_le_prod (fun i hi => (hpos i hi).le)
        intro i hi
        have : (q : ℤ) ^ (n - i) ≤ (q : ℤ) ^ n := pow_le_pow_right₀ hq1.le (Nat.sub_le n i)
        linarith
    _ = (q : ℤ) ^ (n * j) := by rw [Finset.prod_const, Finset.card_range, ← pow_mul]

theorem one_le_prod (q j : ℕ) (hq : 2 ≤ q) : 1 ≤ ∏ i ∈ Finset.range j, ((q : ℤ) ^ (i + 1) - 1) := by
  have hq1 : (1 : ℤ) < q := by exact_mod_cast (by omega : 1 < q)
  have h1 : ∀ i ∈ Finset.range j, (1 : ℤ) ≤ (q : ℤ) ^ (i + 1) - 1 := by
    intro i _
    have : (q : ℤ) ≤ (q : ℤ) ^ (i + 1) := by
      calc (q : ℤ) = (q : ℤ) ^ 1 := (pow_one _).symm
        _ ≤ (q : ℤ) ^ (i + 1) := pow_le_pow_right₀ hq1.le (by omega)
    linarith
  calc (1 : ℤ) = ∏ _i ∈ Finset.range j, (1 : ℤ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) h1

end GlobalTheory.TjCount

open GlobalTheory.TjCount in

theorem GlobalTheory.TjCount.tj_cosets_finite_card_le : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ϖ : w.adicCompletion E), Formalism.UG.IsUnifV E w ϖ → ∀ j ≤ n, {q : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w n | Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j q.out ≠ 0}.Finite ∧ Nat.card {q : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w n // Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j q.out ≠ 0} ≤ Formalism.UG.qV E w ^ (n * j) := by
  intro E _ _ w n ϖ hϖ j hj
  have h := Formalism.UG.P.Tj_double_coset_decomposition E w n ϖ (GlobalTheory.LFun.mem_Ov_of_isUnifV hϖ) hϖ j hj
  have hq : 2 ≤ Formalism.UG.qV E w := GlobalTheory.LFun.one_lt_absNorm w
  have hcard : Nat.card {q : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w n //
      Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j q.out ≠ 0} =
      Nat.card {x : GL (Fin n) (w.adicCompletion E) ⧸ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov E w) |
        Formalism.UG.Tj ℤ n (Formalism.UG.Ov E w) ϖ j x.out ≠ 0} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => Tj_complex_ne_zero_iff _ _ _ _ _)
  obtain ⟨hP, hB⟩ := prod_le_pow (Formalism.UG.qV E w) n j hq hj
  have hA := one_le_prod (Formalism.UG.qV E w) j hq
  rw [← hcard] at h
  set C := Nat.card {q : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w n //
      Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j q.out ≠ 0} with hC
  have hCpos : 0 < C := by
    rcases Nat.eq_zero_or_pos C with h0 | h0
    · rw [h0] at h; simp at h; linarith
    · exact h0
  have hle : (C : ℤ) ≤ (Formalism.UG.qV E w : ℤ) ^ (n * j) := by
    have : (C : ℤ) ≤ (C : ℤ) * ∏ i ∈ Finset.range j, ((Formalism.UG.qV E w : ℤ) ^ (i + 1) - 1) :=
      le_mul_of_one_le_right (by positivity) hA
    linarith
  refine ⟨?_, by exact_mod_cast hle⟩
  have : Finite {q : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w n //
      Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j q.out ≠ 0} := Nat.finite_of_card_ne_zero hCpos.ne'
  exact Set.finite_coe_iff.mp (by exact this)
