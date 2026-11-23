import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov.LowDim

variable {n m : ℕ} {W : ℕ → Submodule ℂ (Fin n → ℂ)} {r : ℕ → ℕ}
  {U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ}

theorem block_eq_zero (hB : Biorth r m U (fun b => (U b)ᴴ)) {s : ℕ} (hs : m ≤ s) : U s = 0 := by
  obtain ⟨-, h2, h3⟩ := hB
  calc U s = (∑ b ∈ range m, U b * (U b)ᴴ) * U s := by rw [h3, Matrix.one_mul]
    _ = 0 := by
      rw [Matrix.sum_mul]
      refine Finset.sum_eq_zero fun b hb => ?_
      have hb' : b ≠ s := by have := Finset.mem_range.1 hb; omega
      rw [Matrix.mul_assoc, h2 b s hb', Matrix.mul_zero]

theorem mem_lowers_iff_blocks (hB : Biorth r m U (fun b => (U b)ᴴ))
    (hW : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0) (c : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) :
    Y ∈ lowers W c ↔ ∀ s t, t ≤ s + c → (U s)ᴴ * Y * U t = 0 := by
  obtain ⟨-, h2, h3⟩ := hB
  rw [mem_lowers]
  constructor
  · intro h s t hst
    refine Matrix.ext_of_mulVec_single fun j => ?_
    have hy : U t *ᵥ Pi.single j 1 ∈ W (s + c + 1) := by
      rw [hW]
      intro b hb
      rw [Matrix.mulVec_mulVec, h2 b t (by omega), Matrix.zero_mulVec]
    have := (hW _ _).1 (h s _ hy) s le_rfl
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this
    rw [this, Matrix.zero_mulVec]
  · intro h b y hy
    rw [hW]
    intro s hs
    have e : (U s)ᴴ *ᵥ Y *ᵥ y = ((U s)ᴴ * Y * ∑ t ∈ range m, U t * (U t)ᴴ) *ᵥ y := by
      rw [h3, Matrix.mul_one, Matrix.mulVec_mulVec]
    rw [e, Matrix.mul_sum, Matrix.sum_mulVec]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [← Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
    by_cases hst : t ≤ s + c
    · rw [h s t hst, Matrix.zero_mulVec]
    · rw [(hW _ _).1 hy t (by omega), Matrix.mulVec_zero]

noncomputable def layer (m : ℕ) (U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ) (c : ℕ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ∀ b : Fin m, Matrix (Fin (r b)) (Fin (r (b + c + 1))) ℂ where
  toFun Y b := (U b)ᴴ * Y * U (b + c + 1)
  map_add' Y Z := by
    funext b
    simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' a Y := by
    funext b
    simp

end GlobalTheory.RadCov.LowDim

namespace GlobalTheory.RadCov

open LowDim in

theorem finrank_lowers_eq_succ_add (n m : ℕ) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (r : ℕ → ℕ)
    (U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ) (hB : Biorth r m U (fun b => (U b)ᴴ))
    (hW : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0) (c : ℕ) :
    Module.finrank ℂ (lowers W c) = Module.finrank ℂ (lowers W (c + 1)) +
      ∑ b ∈ Finset.range m, r b * r (b + c + 1) := by
  have hle : lowers W (c + 1) ≤ lowers W c := by
    intro Y hY
    rw [mem_lowers_iff_blocks hB hW] at hY ⊢
    exact fun s t hst => hY s t (by omega)
  let φ := (layer m U c).domRestrict (lowers W c)
  have hker : LinearMap.ker φ = (lowers W (c + 1)).comap (lowers W c).subtype := by
    ext ⟨Y, hY⟩
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply,
      mem_lowers_iff_blocks hB hW]
    rw [mem_lowers_iff_blocks hB hW] at hY
    constructor
    · intro h s t hst
      by_cases h' : t ≤ s + c
      · exact hY s t h'
      · obtain rfl : t = s + c + 1 := by omega
        by_cases hs : s < m
        · exact congrFun h ⟨s, hs⟩
        · rw [block_eq_zero hB (not_lt.1 hs)]
          simp
    · intro h
      funext b
      exact h b (b + c + 1) le_rfl
  have hrange : LinearMap.range φ = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro Z
    obtain ⟨h1, h2, -⟩ := id hB
    have key : ∀ s t, (U s)ᴴ * (∑ b : Fin m, U b * Z b * (U (b + c + 1))ᴴ) * U t
        = ∑ b : Fin m, ((U s)ᴴ * U b) * Z b * ((U (b + c + 1))ᴴ * U t) := by
      intro s t
      rw [Matrix.mul_sum, Matrix.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by simp only [Matrix.mul_assoc]
    refine ⟨⟨∑ b : Fin m, U b * Z b * (U (b + c + 1))ᴴ, ?_⟩, ?_⟩
    · rw [mem_lowers_iff_blocks hB hW]
      intro s t hst
      rw [key]
      refine Finset.sum_eq_zero fun b _ => ?_
      by_cases hb : s = b
      · rw [h2 (b + c + 1) t (by omega), Matrix.mul_zero]
      · rw [h2 s b hb, Matrix.zero_mul, Matrix.zero_mul]
    · funext s
      change (U s)ᴴ * (∑ b : Fin m, U b * Z b * (U (b + c + 1))ᴴ) * U (s + c + 1) = Z s
      rw [key, Finset.sum_eq_single s]
      · rw [h1, h1, Matrix.one_mul, Matrix.mul_one]
      · intro b _ hb
        rw [h2 s b (fun h => hb (Fin.ext h.symm)), Matrix.zero_mul, Matrix.zero_mul]
      · simp
  have h := LinearMap.finrank_range_add_finrank_ker φ
  rw [hker, hrange, finrank_top, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq,
    Module.finrank_pi_fintype] at h
  rw [← h, add_comm, ← Fin.sum_univ_eq_sum_range (fun b => r b * r (b + c + 1)) m]
  simp [Module.finrank_matrix]

end GlobalTheory.RadCov
