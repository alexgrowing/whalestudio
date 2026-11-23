import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory.UnipKill

theorem exists_nat_mul_isIntegral_iwasawa_decomposition (E : Type) [Field E] [NumberField E] (c : E) :
    ∃ a : ℕ, 0 < a ∧ IsIntegral ℤ ((a : E) * c) := by
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ (L := E) {c}
  have hc := h c (Finset.mem_singleton_self c)
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg y
  · refine ⟨n, Nat.pos_of_ne_zero (by rintro rfl; simp at hy), ?_⟩
    have : ((n : ℕ) : E) * c = ((n : ℤ)) • c := by rw [zsmul_eq_mul]; push_cast; rfl
    rw [this]; exact hc
  · refine ⟨n, Nat.pos_of_ne_zero (by rintro rfl; simp at hy), ?_⟩
    have : ((n : ℕ) : E) * c = -((-(n : ℤ)) • c) := by rw [zsmul_eq_mul]; push_cast; ring
    rw [this]; exact hc.neg

theorem exists_nat_smul_mem_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
    (X : Data E N) (v : Fin N → E), ∃ d : ℕ, 0 < d ∧ (d : E) • v ∈ X.Λ := by
  intro E _ _ _ N X v
  have hv : v ∈ Submodule.span E (X.Λ : Set (Fin N → E)) := by rw [X.Λ_span]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d1, hd1, h1⟩ := hx
    obtain ⟨d2, hd2, h2⟩ := hy
    refine ⟨d1 * d2, Nat.mul_pos hd1 hd2, ?_⟩
    have e : ((d1 * d2 : ℕ) : E) • (x + y) = d2 • ((d1 : E) • x) + d1 • ((d2 : E) • y) := by
      simp only [← Nat.cast_smul_eq_nsmul E, smul_smul, smul_add]
      push_cast; congr 1 <;> congr 1 <;> ring
    rw [e]
    exact X.Λ.add_mem (X.Λ.nsmul_mem h1 _) (X.Λ.nsmul_mem h2 _)
  | smul c x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨a, ha, hi⟩ := exists_nat_mul_isIntegral_iwasawa_decomposition E c
    refine ⟨a * d, Nat.mul_pos ha hd, ?_⟩
    let k : 𝓞 E := ⟨(a : E) * c, hi⟩
    have e : ((a * d : ℕ) : E) • (c • x) = k • ((d : E) • x) := by
      rw [← algebraMap_smul E k ((d : E) • x), smul_smul, smul_smul]
      show _ = (((a : E) * c) * (d : E)) • x
      push_cast; congr 1; ring
    rw [e]
    exact X.Λ.smul_mem k h

end GlobalTheory.UnipKill
