import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
open NumberField Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.DenClear

variable {E : Type} [Field E] [NumberField E]

theorem exists_natMul_isIntegral (c : E) : ∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : E) * c) := by
  obtain ⟨y, hy, hi⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ) ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c))
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rcases Int.natAbs_eq y with h | h
  · rw [h, zsmul_eq_mul] at hi
    simpa using hi
  · rw [h, zsmul_eq_mul] at hi
    have := hi.neg
    simpa using this

theorem intSmul_eq {r : ℕ} (a : 𝓞 E) (w : Fin r → E) : a • w = (a : E) • w := by
  rw [← algebraMap_smul E a w]

theorem exists_natSmul_mem {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E)) (v : Fin r → E)
    (hv : v ∈ Submodule.span E (Λ : Set (Fin r → E))) : ∃ n : ℕ, 0 < n ∧ (n : E) • v ∈ Λ := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    have e : ((n * m : ℕ) : E) • (x + y) = m • ((n : E) • x) + n • ((m : E) • y) := by
      simp only [Nat.cast_mul, smul_add, ← Nat.cast_smul_eq_nsmul E, smul_smul]
      congr 1 <;> congr 1 <;> ring
    rw [e]
    exact Λ.add_mem (Λ.nsmul_mem hnx m) (Λ.nsmul_mem hmy n)
  | smul c x _ hx =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hc⟩ := exists_natMul_isIntegral c
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    obtain ⟨a, ha⟩ : ∃ a : 𝓞 E, (a : E) = (m : E) * c := ⟨⟨_, (mem_integralClosure_iff ℤ E).2 hc⟩, rfl⟩
    have e : ((m * n : ℕ) : E) • (c • x) = a • ((n : E) • x) := by
      rw [intSmul_eq, ha, smul_smul, smul_smul]
      congr 1
      push_cast
      ring
    rw [e]
    exact Λ.smul_mem _ hnx

variable [IsCMField E]

theorem exists_natSmul_mem_lieLat : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), Λ.FG →
    Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → ∀ X : Matrix (Fin r) (Fin r) E, X.trace = 0 →
    (∀ x y, herm G (X *ᵥ x) y + herm G x (X *ᵥ y) = 0) → ∃ N : ℕ, 0 < N ∧ (N : E) • X ∈ lieLat G Λ := by
  intro E _ _ _ r G Λ hfg hspan X htr hskew
  obtain ⟨S, hS⟩ := hfg
  have hv : ∀ s : Fin r → E, ∃ n : ℕ, 0 < n ∧ (n : E) • (X *ᵥ s) ∈ Λ := fun s =>
    exists_natSmul_mem Λ _ (by rw [hspan]; trivial)
  choose n hn hnX using hv
  refine ⟨∏ s ∈ S, n s, Finset.prod_pos fun s _ => hn s, ?_, ?_, ?_⟩
  · rw [trace_smul, htr, smul_zero]
  · intro x y
    have h := hskew x y
    simp only [herm, cc, smul_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast] at h ⊢
    have e1 : ∀ a b, (↑(∏ s ∈ S, n s) * (X *ᵥ x) a) * G a b * (IsCMField.complexConj E) (y b) =
        (↑(∏ s ∈ S, n s) : E) * ((X *ᵥ x) a * G a b * (IsCMField.complexConj E) (y b)) := fun a b => by ring
    have e2 : ∀ a b, x a * G a b * ((↑(∏ s ∈ S, n s) : E) * (IsCMField.complexConj E) ((X *ᵥ y) b)) =
        (↑(∏ s ∈ S, n s) : E) * (x a * G a b * (IsCMField.complexConj E) ((X *ᵥ y) b)) := fun a b => by ring
    simp only [e1, e2, ← Finset.mul_sum]
    rw [← mul_add, h, mul_zero]
  · intro x hx
    rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem s hs =>
      rw [smul_mulVec]
      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n hs
      rw [hk, Nat.cast_mul, mul_comm, ← smul_smul, Nat.cast_smul_eq_nsmul]
      exact Λ.nsmul_mem (hnX s) k
    | zero => simp
    | add x y _ _ hx hy => rw [mulVec_add]; exact Λ.add_mem hx hy
    | smul a x _ hx =>
      rw [intSmul_eq, mulVec_smul, ← intSmul_eq]
      exact Λ.smul_mem a hx

end GlobalTheory.DenClear
