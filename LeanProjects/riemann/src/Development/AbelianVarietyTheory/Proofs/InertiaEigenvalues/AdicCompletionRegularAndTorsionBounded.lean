import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemPowOfMulMemPowBoundedTorsionStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.ComplLD

theorem smodEq_iff {Q : Type} [CommRing Q] (I : Ideal Q) (n : ℕ) (x y : Q) :
    x ≡ y [SMOD (I ^ n • ⊤ : Submodule Q Q)] ↔ x - y ∈ I ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

theorem eq_zero_of_mem {Q : Type} [CommRing Q] (I : Ideal Q) [IsHausdorff I Q] (x : Q)
    (h : ∀ n, x ∈ I ^ n) : x = 0 :=
  IsHausdorff.haus' x fun n => (smodEq_iff I n x 0).2 (by simpa using h n)

theorem exists_lim {Q : Type} [CommRing Q] (I : Ideal Q) [IsPrecomplete I Q] (f : ℕ → Q)
    (h : ∀ m n, m ≤ n → f n - f m ∈ I ^ m) : ∃ z, ∀ n, f n - z ∈ I ^ n := by
  obtain ⟨z, hz⟩ := IsPrecomplete.prec' (I := I) f fun {m n} hmn =>
    (smodEq_iff I m _ _).2 (by rw [show f m - f n = -(f n - f m) by ring]; exact neg_mem (h m n hmn))
  exact ⟨z, fun n => (smodEq_iff I n _ _).1 (hz n)⟩

theorem regular_and_torsion_bounded : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [CommRing L] (Q : Type) [CommRing Q] (i : L →+* Q) (d : L) (N : ℕ), d ∈ nonZeroDivisors L → (∀ (x : L) (m : ℕ), (l : L) ^ m * x ∈ Ideal.span {d} → (l : L) ^ N * x ∈ Ideal.span {d}) → IsCompl i (Ideal.span {(l : L)} ⊔ Ideal.span {d}) → i d ∈ nonZeroDivisors Q ∧ ∀ (x : Q) (m : ℕ), (l : Q) ^ m * x ∈ Ideal.span {i d} → (l : Q) ^ N * x ∈ Ideal.span {i d} := by
  intro l _ L _ Q _ i d N hd hbd hc
  set J : Ideal L := Ideal.span {(l : L)} ⊔ Ideal.span {d} with hJ
  set I : Ideal Q := J.map i with hI
  haveI : IsAdicComplete I Q := hc.complete
  have hpow : ∀ n, (J ^ n).map i = I ^ n := fun n => Ideal.map_pow _ _ _
  have surj : ∀ (x : Q) n, ∃ a, x - i a ∈ I ^ n := fun x n => by
    obtain ⟨a, ha⟩ := hc.surj x n; exact ⟨a, by rwa [← hpow]⟩
  have ker : ∀ a n, i a ∈ I ^ n → a ∈ J ^ n := fun a n h => hc.ker a n (by rwa [hpow])
  have strict : ∀ n z, i d * z ∈ I ^ (2 * (n + N + 1)) → z ∈ I ^ n := by
    intro n z hz
    obtain ⟨a, ha⟩ := surj z (2 * (n + N + 1))
    have h1 : i (d * a) ∈ I ^ (2 * (n + N + 1)) := by
      have e : i (d * a) = i d * z - i d * (z - i a) := by rw [map_mul]; ring
      rw [e]; exact sub_mem hz (Ideal.mul_mem_left _ _ ha)
    have h2 := GlobalTheory.T.mem_pow_of_mul_mem_pow_bounded_torsion l L d N hd hbd n a (ker _ _ h1)
    have h3 : i a ∈ I ^ n := by rw [← hpow]; exact Ideal.mem_map_of_mem i h2
    have h4 : z - i a ∈ I ^ n := Ideal.pow_le_pow_right (by omega) ha
    simpa using add_mem h4 h3
  have reg : i d ∈ nonZeroDivisors Q := by
    rw [mem_nonZeroDivisors_iff]
    exact ⟨fun z hz => eq_zero_of_mem I z fun n => strict n z (by rw [hz]; exact zero_mem _),
      fun z hz => eq_zero_of_mem I z fun n => strict n z (by rw [mul_comm (i d) z, hz]; exact zero_mem _)⟩
  have closed : ∀ x, (∀ n, ∃ z, x - i d * z ∈ I ^ n) → x ∈ Ideal.span {i d} := by
    intro x hx
    choose z hz using fun n => hx (2 * (n + N + 1))
    obtain ⟨w, hw⟩ := exists_lim I z fun m n hmn => strict m _ (by
      have e : i d * (z n - z m) = (x - i d * z m) - (x - i d * z n) := by ring
      rw [e]; exact sub_mem (hz m) (Ideal.pow_le_pow_right (by omega) (hz n)))
    have h0 : x - i d * w = 0 := eq_zero_of_mem I _ fun n => by
      have e : x - i d * w = (x - i d * z n) + i d * (z n - w) := by ring
      rw [e]; exact add_mem (Ideal.pow_le_pow_right (by omega) (hz n)) (Ideal.mul_mem_left _ _ (hw n))
    exact Ideal.mem_span_singleton'.2 ⟨w, by rw [mul_comm]; exact (sub_eq_zero.1 h0).symm⟩
  refine ⟨reg, fun x m hx => closed _ fun n => ?_⟩
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hx
  obtain ⟨a, ha⟩ := surj x (m + n + 1)
  obtain ⟨b, hb⟩ := surj y (m + n + 1)
  have h1 : i ((l : L) ^ m * a - d * b) ∈ I ^ (m + n + 1) := by
    have e : i ((l : L) ^ m * a - d * b) = -((l : Q) ^ m * (x - i a)) + i d * (y - i b) := by
      rw [map_sub, map_mul, map_mul, map_pow, map_natCast]; linear_combination (-1 : Q) * hy
    rw [e]; exact add_mem (neg_mem (Ideal.mul_mem_left _ _ ha)) (Ideal.mul_mem_left _ _ hb)
  have h2 : (l : L) ^ m * a - d * b ∈ Ideal.span {(l : L) ^ (m + n)} ⊔ Ideal.span {d} := by
    have hle : J ^ (m + n + 1) ≤ Ideal.span {(l : L)} ^ (m + n) ⊔ Ideal.span {d} ^ 1 :=
      Ideal.sup_pow_add_le_pow_sup_pow
    simpa [Ideal.span_singleton_pow] using hle (ker _ _ h1)
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 h2
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hu
  obtain ⟨e, rfl⟩ := Ideal.mem_span_singleton'.1 hv
  have h3 : (l : L) ^ m * (a - (l : L) ^ n * c) ∈ Ideal.span {d} :=
    Ideal.mem_span_singleton'.2 ⟨b + e, by linear_combination huv⟩
  obtain ⟨f, hf⟩ := Ideal.mem_span_singleton'.1 (hbd _ _ h3)
  refine ⟨i f, ?_⟩
  have hf' := congrArg i hf
  simp only [map_mul, map_pow, map_natCast, map_sub] at hf'
  have e : (l : Q) ^ N * x - i d * i f = (l : Q) ^ N * (x - i a) + i ((l : L) ^ (N + n) * c) := by
    rw [map_mul, map_pow, map_natCast]; linear_combination (-1 : Q) * hf'
  rw [e]
  refine add_mem (Ideal.pow_le_pow_right (by omega) (Ideal.mul_mem_left _ _ ha)) ?_
  rw [← hpow]
  refine Ideal.mem_map_of_mem i (Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right (by omega : n ≤ N + n)
    (Ideal.pow_mem_pow (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) (N + n))))

end GlobalTheory.BSP.ComplLD
