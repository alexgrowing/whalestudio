import Development.EtaleCohomology.EtaleSheaves.LZIdemSumApprox

noncomputable section
open LateralTheory.E.StandardEtaleChartsIdempotentGluing

namespace LateralTheory.E.LZIdemSumNoetherian

def NoetherianLocalChartOverlapFiniteComplement : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (K : Type) [Field K]
  [Algebra A K] (B C : Subalgebra A K) (t : K), Charts B C t → B.FG → C.FG →
  ∃ N : Submodule A K, N.FG ∧ Subalgebra.toSubmodule (AdjoinInv B t) ≤
    Subalgebra.toSubmodule B ⊔ Subalgebra.toSubmodule C ⊔ N

def LZIdemPow : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] (K : Type) [Field K] [Algebra A K]
  (B C : Subalgebra A K) (t : K), Charts B C t → ∀ e f : K, IdemPair B C t e f → ∀ k : ℕ,
  ∃ b ∈ B, ∃ c ∈ C, e - b ∈ mS B ∧ c - f ∈ mS C ∧
    b - c ∈ (IsLocalRing.maximalIdeal A ^ k) • Subalgebra.toSubmodule (AdjoinInv B t)

def LZARStep : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (M : Type) [AddCommGroup M]
  [Module A M] (N P : Submodule A M), N.FG →
  ∃ k : ℕ, 1 ≤ k ∧ (IsLocalRing.maximalIdeal A ^ k) • N ⊓ P ≤ IsLocalRing.maximalIdeal A • P

theorem goal_of (h1 : NoetherianLocalChartOverlapFiniteComplement) (h2 : LZIdemPow) (h3 : LZARStep) :
    LateralTheory.E.IdempotentLiftingAlt.LZIdemSumNoeth := by
  intro A _ _ _ K _ _ B C t hc hB hC e f hp
  obtain ⟨N, hN, hD⟩ := h1 A K B C t hc hB hC
  obtain ⟨k, hk, hAR⟩ := h3 A K N (Subalgebra.toSubmodule B ⊔ Subalgebra.toSubmodule C) hN
  obtain ⟨b, hb, c, hcC, heb, hcf, hbc⟩ := h2 A K B C t hc e f hp k
  have hmk : IsLocalRing.maximalIdeal A ^ k ≤ IsLocalRing.maximalIdeal A := Ideal.pow_le_self (by omega)
  have hbc' := Submodule.smul_mono (le_refl (IsLocalRing.maximalIdeal A ^ k)) hD hbc
  rw [Submodule.smul_sup, Submodule.smul_sup] at hbc'
  obtain ⟨x, hx, n, hn, hxn⟩ := Submodule.mem_sup.mp hbc'
  obtain ⟨β, hβ, γ, hγ, hβγ⟩ := Submodule.mem_sup.mp hx
  have hβB : β ∈ B := Submodule.smul_le_right hβ
  have hγC : γ ∈ C := Submodule.smul_le_right hγ
  have hnP : n ∈ Subalgebra.toSubmodule B ⊔ Subalgebra.toSubmodule C := by
    refine Submodule.mem_sup.mpr ⟨b - β, B.sub_mem hb hβB, -(c + γ), C.neg_mem (C.add_mem hcC hγC), ?_⟩
    linear_combination -hxn - hβγ
  have hnm := hAR ⟨hn, hnP⟩
  rw [Submodule.smul_sup] at hnm
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hnm
  have hβm : β ∈ mS B := Submodule.smul_mono_left hmk hβ
  have hγm : γ ∈ mS C := Submodule.smul_mono_left hmk hγ
  have hum : u ∈ mS B := hu
  have hvm : v ∈ mS C := hv
  refine Submodule.mem_sup.mpr ⟨(e - b) + β + u, (mS B).add_mem ((mS B).add_mem heb hβm) hum,
    γ + v + (c - f), (mS C).add_mem ((mS C).add_mem hγm hvm) hcf, ?_⟩
  linear_combination hxn + hβγ + huv

end LateralTheory.E.LZIdemSumNoetherian
