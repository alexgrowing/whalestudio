import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialSmoothInChartStatement

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff Topology

namespace GlobalTheory

theorem isBoundary_sec_ne_zero {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {m : ℕ} (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ) (D : Fin m → Set X)
    (hB : IsBoundary A L s D) (i : Fin m) (y0 : X) (hy0 : y0 ∉ D i) : s i y0 y0 ≠ 0 := by
  obtain ⟨-, -, hsnc, -⟩ := hB i
  obtain ⟨ψ', -, hx, -, σ, -, hW, u, -, hu0, hs⟩ := hsnc y0
  rw [hs y0 hx]
  refine mul_ne_zero (hu0 y0 hx) ?_
  refine Finset.prod_ne_zero_iff.mpr fun k _ => ?_
  rcases hk : σ k with _ | j
  · simp
  · simp only
    by_cases hki : k = i
    · subst hki
      simp only [Pi.single_eq_same, pow_one]
      intro h0
      have : y0 ∈ D k ∩ ψ'.source := by
        rw [hW k]; exact ⟨hx, j, hk, h0⟩
      exact hy0 this.1
    · simp [Pi.single_eq_of_ne hki]

theorem rComp_contDiffAt_compatChart {e : ℕ} {X : Type} [TopologicalSpace X]
    (A : FinHolAtlas e X) {m : ℕ} (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ)
    (D : Fin m → Set X) (hB : IsBoundary A L s D) (i : Fin m)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (hψ : IsCompatChart A ψ)
    (z : Fin e → ℂ) (hz : z ∈ ψ.target) (hzD : ψ.symm z ∉ D i) :
    ContDiffAt ℝ ∞ (rComp L s i ∘ ψ.symm) z := by
  set y0 := ψ.symm z with hy0def
  obtain ⟨hpot, hsec, -, -⟩ := hB i
  have hne : s i y0 y0 ≠ 0 := isBoundary_sec_ne_zero A L s D hB i y0 hzD

  have hΦ : ContDiffAt ℝ ∞ ((L i).φ y0 ∘ ψ.symm) z := GlobalTheory.T.potential_smooth_in_chart A (L i) hpot ψ hψ z hz

  obtain ⟨j, hj⟩ := A.cover y0
  have h2 : AnalyticAt ℂ (A.chart j ∘ ψ.symm) z := (hψ j).2 z ⟨hz, hj⟩
  have h1 : AnalyticAt ℂ (s i y0 ∘ (A.chart j).symm) ((A.chart j ∘ ψ.symm) z) := by
    refine hsec.1 y0 j _ ⟨(A.chart j).map_source hj, ?_⟩
    simp only [Function.comp_apply, Set.mem_preimage, ← hy0def, (A.chart j).left_inv hj]
    exact (L i).mem_U _
  have hev : ∀ᶠ y in 𝓝 z, ψ.symm y ∈ (A.chart j).source :=
    (ψ.continuousAt_symm hz).eventually ((A.chart j).open_source.mem_nhds hj)
  have hS : ContDiffAt ℝ ∞ (s i y0 ∘ ψ.symm) z := by
    refine ((h1.comp h2).contDiffAt (n := ∞)).restrict_scalars ℝ |>.congr_of_eventuallyEq ?_
    filter_upwards [hev] with y hy
    simp only [Function.comp_apply, (A.chart j).left_inv hy]
  have hSz : (s i y0 ∘ ψ.symm) z ≠ 0 := hne
  have hG : ContDiffAt ℝ ∞ (fun y => Real.exp 1 -
      Real.log ((‖(s i y0 ∘ ψ.symm) y‖ * Real.exp (-((L i).φ y0 ∘ ψ.symm) y)) ^ 2)) z := by
    refine contDiffAt_const.sub (ContDiffAt.log ?_ ?_)
    · exact ((hS.norm ℝ hSz).mul hΦ.neg.exp).pow 2
    · have : 0 < ‖(s i y0 ∘ ψ.symm) z‖ := norm_pos_iff.mpr hSz
      positivity
  refine hG.congr_of_eventuallyEq ?_
  have hevU : ∀ᶠ y in 𝓝 z, ψ.symm y ∈ (L i).U y0 :=
    (ψ.continuousAt_symm hz).eventually (((L i).isOpen_U y0).mem_nhds ((L i).mem_U y0))
  filter_upwards [hevU] with y hy
  have hg := hsec.2 (ψ.symm y) y0 (ψ.symm y) ⟨(L i).mem_U _, hy⟩
  simp only [Function.comp_apply, rComp, normSec]
  rw [hg]

end GlobalTheory
