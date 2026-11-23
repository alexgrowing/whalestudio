import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory

theorem boundary_chart_facts {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {m : ℕ}
    (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ) (D : Fin m → Set X)
    (hB : IsBoundary A L s D) (i : Fin m) (ψ : OpenPartialHomeomorph X (Fin e → ℂ))
    (hψ : IsCompatChart A ψ) (z : Fin e → ℂ) (hz : z ∈ ψ.target) (hD : ψ.symm z ∉ D i) :
    AnalyticAt ℂ (s i (ψ.symm z) ∘ ψ.symm) z ∧ s i (ψ.symm z) (ψ.symm z) ≠ 0 ∧
      (fun y => normSec (L i) (s i) (ψ.symm y) ^ 2) =ᶠ[nhds z]
        (fun y => ‖(s i (ψ.symm z) ∘ ψ.symm) y‖ ^ 2 *
          Real.exp (-2 * ((L i).φ (ψ.symm z) ∘ ψ.symm) y)) := by
  obtain ⟨_, ⟨hsecH, hsecG⟩, hsnc, _⟩ := hB i
  set x := ψ.symm z with hx
  refine ⟨?_, ?_, ?_⟩
  ·
    obtain ⟨j, hj⟩ := A.cover x
    have h1 : AnalyticAt ℂ (s i x ∘ (A.chart j).symm) (A.chart j x) := by
      apply hsecH x j
      refine ⟨(A.chart j).map_source hj, ?_⟩
      show (A.chart j).symm (A.chart j x) ∈ (L i).U x
      rw [(A.chart j).left_inv hj]
      exact (L i).mem_U x
    have h2 : AnalyticAt ℂ (A.chart j ∘ ψ.symm) z := (hψ j).2 z ⟨hz, hj⟩
    have h3 : AnalyticAt ℂ ((s i x ∘ (A.chart j).symm) ∘ (A.chart j ∘ ψ.symm)) z :=
      AnalyticAt.comp h1 h2
    refine h3.congr ?_
    have hO : IsOpen (ψ.target ∩ ψ.symm ⁻¹' (A.chart j).source) :=
      ψ.isOpen_inter_preimage_symm (A.chart j).open_source
    filter_upwards [hO.mem_nhds ⟨hz, hj⟩] with y hy
    simp only [Function.comp]
    rw [(A.chart j).left_inv hy.2]
  ·
    obtain ⟨ψ', _, hxψ', _, σ, _, hDσ, u, _, hu0, hs⟩ := hsnc x
    rw [hs x hxψ']
    refine mul_ne_zero (hu0 x hxψ') ?_
    rw [Finset.prod_ne_zero_iff]
    intro k _
    cases hk : σ k with
    | none => simp
    | some a =>
      simp only
      by_cases hki : k = i
      · subst hki
        rw [Pi.single_eq_same, pow_one]
        intro h0
        apply hD
        have : x ∈ {y ∈ ψ'.source | ∃ a, σ k = some a ∧ ψ' y a = 0} := ⟨hxψ', a, hk, h0⟩
        rw [← hDσ k] at this
        exact this.1
      · rw [Pi.single_eq_of_ne hki, pow_zero]
        exact one_ne_zero
  ·
    have hO : IsOpen (ψ.target ∩ ψ.symm ⁻¹' (L i).U x) :=
      ψ.isOpen_inter_preimage_symm ((L i).isOpen_U x)
    have hzO : z ∈ ψ.target ∩ ψ.symm ⁻¹' (L i).U x := ⟨hz, (L i).mem_U x⟩
    filter_upwards [hO.mem_nhds hzO] with y hy
    have hg := hsecG (ψ.symm y) x (ψ.symm y) ⟨(L i).mem_U _, hy.2⟩
    simp only [normSec, Function.comp]
    rw [hg, mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring

end GlobalTheory
