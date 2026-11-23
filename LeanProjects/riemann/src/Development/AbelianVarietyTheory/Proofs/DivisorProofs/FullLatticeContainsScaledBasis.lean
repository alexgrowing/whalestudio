import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPart
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
open NumberField ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.LieHt GlobalTheory.LieRead

set_option autoImplicit false

namespace GlobalTheory.LatNat

theorem natMul_integral {K : Type} [Field K] [NumberField K] (c : K) :
    ∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : K) * c) := by
  have hc : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (.of_finite ℚ c)
  obtain ⟨y, hy, hint⟩ := hc.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rcases Int.natAbs_eq y with h | h
  · have : ((y.natAbs : ℕ) : K) * c = y • c := by
      conv_rhs => rw [h]
      simp [zsmul_eq_mul]
    rw [this]; exact hint
  · have : ((y.natAbs : ℕ) : K) * c = -(y • c) := by
      conv_rhs => rw [h]
      simp [zsmul_eq_mul]
    rw [this]; exact hint.neg

def natSat {K : Type} [Field K] [NumberField K] {g : ℕ} (L : Submodule (𝓞 K) (Fin g → K)) :
    Submodule K (Fin g → K) where
  carrier := {x | ∃ n : ℕ, 0 < n ∧ n • x ∈ L}
  add_mem' := by
    rintro x y ⟨n₁, h₁, hx⟩ ⟨n₂, h₂, hy⟩
    refine ⟨n₁ * n₂, Nat.mul_pos h₁ h₂, ?_⟩
    have : (n₁ * n₂) • (x + y) = n₂ • (n₁ • x) + n₁ • (n₂ • y) := by
      rw [smul_add, smul_smul n₂ n₁, smul_smul n₁ n₂, mul_comm n₂ n₁]
    rw [this]
    exact L.add_mem (L.toAddSubmonoid.nsmul_mem hx n₂) (L.toAddSubmonoid.nsmul_mem hy n₁)
  zero_mem' := ⟨1, one_pos, by simp⟩
  smul_mem' := by
    rintro c x ⟨n, hn, hx⟩
    obtain ⟨m, hm, hint⟩ := natMul_integral c
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    let a : 𝓞 K := ⟨(m : K) * c, hint⟩
    have : (m * n) • (c • x) = a • (n • x) := by
      rw [← algebraMap_smul K a (n • x)]
      show (m * n) • (c • x) = ((m : K) * c) • (n • x)
      rw [← Nat.cast_smul_eq_nsmul K, ← Nat.cast_smul_eq_nsmul K n x, smul_smul, smul_smul]
      congr 1
      push_cast; ring
    rw [this]
    exact L.smul_mem a hx

theorem exists_natMul_single_mem (K : Type) [Field K] [NumberField K] (g : ℕ) (L : Submodule (𝓞 K) (Fin g → K))
    (hL : Full L) : ∃ D : ℕ, 0 < D ∧ ∀ k : Fin g, (D : K) • (Pi.single k 1 : Fin g → K) ∈ L := by
  have hle : Submodule.span K (L : Set (Fin g → K)) ≤ natSat L :=
    Submodule.span_le.2 fun x hx => ⟨1, one_pos, by simpa using hx⟩
  rw [hL.2] at hle
  have hk : ∀ k : Fin g, ∃ n : ℕ, 0 < n ∧ n • (Pi.single k 1 : Fin g → K) ∈ L :=
    fun k => hle (Submodule.mem_top (x := (Pi.single k 1 : Fin g → K)))
  choose n hn hmem using hk
  refine ⟨∏ k, n k, Finset.prod_pos fun k _ => hn k, fun k => ?_⟩
  obtain ⟨q, hq⟩ : n k ∣ ∏ i, n i := Finset.dvd_prod_of_mem n (Finset.mem_univ k)
  rw [Nat.cast_smul_eq_nsmul K, hq, mul_comm, mul_smul]
  exact L.toAddSubmonoid.nsmul_mem (hmem k) q

end GlobalTheory.LatNat
