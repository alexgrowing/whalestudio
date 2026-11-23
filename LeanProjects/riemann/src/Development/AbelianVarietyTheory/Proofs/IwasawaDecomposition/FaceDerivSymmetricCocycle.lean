import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CubeRatio
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfPderivOfBlinKill

open GlobalTheory.RayHoriz.CubeNorm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CubeSeries

open MvPowerSeries

variable {S : Type} [CommRing S] {ρ : Type} [Fintype ρ] [DecidableEq ρ]

theorem pderiv_blin_of_col {K K' : Type} [Fintype K] [DecidableEq K] [Fintype K'] [DecidableEq K']
    (M : K → K' → ℤ) (F : MvPowerSeries (K × ρ) S) (j : K') (k₀ : K)
    (hM : ∀ k, M k j = if k = k₀ then 1 else 0) (r : ρ) :
    pderiv S (j, r) (blin M F) = blin M (pderiv S (k₀, r) F) := by
  rw [pderiv_blin]
  simp [hM, ite_smul, Finset.sum_ite_eq']

theorem faceDeriv_constantCoeff_and_isSymCoc (G : MvPowerSeries (Fin 3 × ρ) S) (hG : IsAddCub G)
    (r : ρ) :
    constantCoeff (faceDeriv G r) = 0 ∧ IsSymCoc (faceDeriv G r) := by
  obtain ⟨h0, h01, h12, hc⟩ := hG
  simp only [linSub_eq_blin] at h0 h01 h12 hc

  have e2 : pderiv S ((2 : Fin 3), r) G =
      blin (fun k i => if i ∈ (![{1}, {0}, {2}] : Fin 3 → Finset (Fin 3)) k then (1 : ℤ) else 0)
        (pderiv S ((2 : Fin 3), r) G) := by
    conv_lhs => rw [← h01]
    exact pderiv_blin_of_col _ _ _ 2 (by intro k; fin_cases k <;> simp) r
  refine ⟨?_, ?_, ?_⟩
  ·
    have e1 : pderiv S ((2 : Fin 3), r) G =
        blin (fun k i => if i ∈ (![{0}, {2}, {1}] : Fin 3 → Finset (Fin 3)) k then (1 : ℤ) else 0)
          (pderiv S ((1 : Fin 3), r) G) := by
      conv_lhs => rw [← h12]
      exact pderiv_blin_of_col _ _ _ 1 (by intro k; fin_cases k <;> simp) r
    have hk : blin (fun k i => if i ∈ (![{0}, {1}, ∅] : Fin 3 → Finset (Fin 3)) k then (1 : ℤ) else 0)
        (pderiv S ((1 : Fin 3), r) G) = 0 := by
      rw [← pderiv_blin_of_col _ _ (1 : Fin 3) 1 (by intro k; fin_cases k <;> simp) r, h0, map_zero]
    have hk' := congrArg constantCoeff hk
    rw [constantCoeff_blin, map_zero] at hk'
    rw [faceDeriv, constantCoeff_blin, e1, constantCoeff_blin, hk']
  ·
    conv_rhs => rw [faceDeriv, e2]
    rw [faceDeriv, blin_blin, blin_blin]
    congr 1
    funext k j
    fin_cases k <;> fin_cases j <;> simp [Fin.sum_univ_three, Fin.sum_univ_two]
  ·
    have key : ∀ (A : Fin 3 → Finset (Fin 4)) (B : Fin 2 → Fin 3 → ℤ),
        (∀ k, (if (3 : Fin 4) ∈ A k then (1 : ℤ) else 0) = if k = 2 then 1 else 0) →
        (∀ k j, ∑ i, (if i ∈ A k then (1 : ℤ) else 0) *
            (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![0, 0, 0]] : Fin 4 → Fin 3 → ℤ) i j =
          ∑ i, (![![1, 0], ![0, 1], ![0, 0]] : Fin 3 → Fin 2 → ℤ) k i * B i j) →
        blin (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![0, 0, 0]] : Fin 4 → Fin 3 → ℤ)
            (pderiv S ((3 : Fin 4), r) (blin (fun k i => if i ∈ A k then (1 : ℤ) else 0) G)) =
          blin B (faceDeriv G r) := by
      intro A B hA hB
      rw [pderiv_blin_of_col (fun k i => if i ∈ A k then (1 : ℤ) else 0) G (3 : Fin 4) (2 : Fin 3) hA r, blin_blin, faceDeriv, blin_blin]
      congr 1
      funext k j
      exact hB k j
    have hc' := congrArg (fun F => blin (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![0, 0, 0]] : Fin 4 → Fin 3 → ℤ)
      (pderiv S ((3 : Fin 4), r) F)) hc
    simp only [map_add, blin_add] at hc'
    rw [key _ (![![1, 1, 0], ![0, 0, 1]]) (by intro k; fin_cases k <;> simp)
        (by intro k j; fin_cases k <;> fin_cases j <;> simp [Fin.sum_univ_four, Fin.sum_univ_three]),
      key _ (![![1, 0, 0], ![0, 1, 0]]) (by intro k; fin_cases k <;> simp)
        (by intro k j; fin_cases k <;> fin_cases j <;> simp [Fin.sum_univ_four, Fin.sum_univ_three]),
      key _ (![![1, 0, 0], ![0, 1, 1]]) (by intro k; fin_cases k <;> simp)
        (by intro k j; fin_cases k <;> fin_cases j <;> simp [Fin.sum_univ_four, Fin.sum_univ_three]),
      key _ (![![0, 1, 0], ![0, 0, 1]]) (by intro k; fin_cases k <;> simp)
        (by intro k j; fin_cases k <;> fin_cases j <;> simp [Fin.sum_univ_four, Fin.sum_univ_three])] at hc'
    exact hc'

end GlobalTheory.CubeSeries

example : ∀ {S : Type} [CommRing S] {ρ : Type} [Fintype ρ] [DecidableEq ρ] (G : MvPowerSeries (Fin 3 × ρ) S), GlobalTheory.CubeSeries.IsAddCub G → ∀ r : ρ, MvPowerSeries.constantCoeff (GlobalTheory.CubeSeries.faceDeriv G r) = 0 ∧ GlobalTheory.CubeSeries.IsSymCoc (GlobalTheory.CubeSeries.faceDeriv G r) :=
  fun G hG r => GlobalTheory.CubeSeries.faceDeriv_constantCoeff_and_isSymCoc G hG r
