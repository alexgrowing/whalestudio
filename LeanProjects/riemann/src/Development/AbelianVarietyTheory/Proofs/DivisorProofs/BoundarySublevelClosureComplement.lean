import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticLogResolution
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt
open scoped ENNReal

namespace GlobalTheory.PFunBoundary

open Filter Topology

theorem continuousAt_of_chart {e : ℕ} {X : Type} [TopologicalSpace X] {β : Type*}
    [TopologicalSpace β] (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) {x : X} (hx : x ∈ ψ.source)
    (f : X → β) (h : ContinuousAt (f ∘ ψ.symm) (ψ x)) : ContinuousAt f x := by
  have h' : ContinuousAt ((f ∘ ψ.symm) ∘ ψ) x := h.comp (ψ.continuousAt hx)
  refine h'.congr ?_
  filter_upwards [ψ.eventually_left_inverse hx] with y hy
  simp [Function.comp, hy]

theorem eventually_normSec_lt {d : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas d X)
    (L : LocPot X) (s : X → X → ℂ) (hpot : IsPotential A L) (hsec : IsSection A L s) {x0 : X}
    (h0 : s x0 x0 = 0) {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ z in 𝓝 x0, normSec L s z < δ := by
  obtain ⟨j, hj⟩ := A.cover x0
  have hU : L.U x0 ∈ 𝓝 x0 := (L.isOpen_U x0).mem_nhds (L.mem_U x0)
  have hmem : A.chart j x0 ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U x0 :=
    ⟨(A.chart j).map_source hj, by simp [(A.chart j).left_inv hj, L.mem_U x0]⟩
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U x0) :=
    (A.chart j).isOpen_inter_preimage_symm (L.isOpen_U x0)
  have hs : ContinuousAt (s x0) x0 :=
    continuousAt_of_chart (A.chart j) hj _ ((hsec.1 x0 j) _ hmem).continuousAt
  have hφ : ContinuousAt (L.φ x0) x0 :=
    continuousAt_of_chart (A.chart j) hj _
      ((hpot.1 x0 j).continuousOn.continuousAt (hopen.mem_nhds hmem))
  have hF : ContinuousAt (fun z => ‖s x0 z‖ * Real.exp (-L.φ x0 z)) x0 :=
    hs.norm.mul (Real.continuous_exp.continuousAt.comp hφ.neg)
  have hlt : ∀ᶠ z in 𝓝 x0, ‖s x0 z‖ * Real.exp (-L.φ x0 z) < δ :=
    hF.eventually (gt_mem_nhds (by simpa [h0] using hδ))
  filter_upwards [hlt, hU] with z hz hzU
  have hglue := hsec.2 z x0 z ⟨L.mem_U z, hzU⟩
  simp only [normSec]
  rw [hglue]
  exact hz

theorem closure_superlevel_subset_compl : ∀ (d : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas d X) (m : ℕ) (α : LocPot X)
    (Λ : Fin m → LocPot X) (σ : Fin m → X → X → ℂ) (c : ℝ),
    IsBoundarySetting A α Λ σ c →
    ∀ a : ℝ, closure {x | x ∈ (boundary σ)ᶜ ∧ -a ≤ pFun Λ σ c x / 2} ⊆ (boundary σ)ᶜ := by
  intro d X _ A m α Λ σ c hB a x0 hx0 hbd
  obtain ⟨-, -, hΛ, hc0, -⟩ := hB
  obtain ⟨i, hi⟩ := hbd
  obtain ⟨hpot, hsec, -, -⟩ := hΛ i
  have hTpos : 0 < Real.exp (2 * a / c) := Real.exp_pos _
  have hev := eventually_normSec_lt A (Λ i) (σ i) hpot hsec hi
    (Real.exp_pos (-Real.exp (2 * a / c)))
  rw [mem_closure_iff_frequently] at hx0
  obtain ⟨z, ⟨hzb, hza⟩, hz⟩ := (hx0.and_eventually hev).exists
  have hne : ∀ k, σ k z z ≠ 0 := fun k hk => hzb ⟨k, hk⟩
  have hpos : ∀ k, 0 < normSec (Λ k) (σ k) z := fun k =>
    mul_pos (norm_pos_iff.2 (hne k)) (Real.exp_pos _)
  have hlog : ∀ k, logNormSec (Λ k) (σ k) z = Real.log (normSec (Λ k) (σ k) z) := fun k => rfl
  have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hnn : ∀ k, 0 ≤ Real.log (rFun (Λ k) (σ k) z) := by
    intro k
    apply Real.log_nonneg
    have := Real.log_nonpos (hpos k).le ((hΛ k).2.2.2 z)
    simp only [rFun, hlog k]
    linarith
  have hi' : Real.log (normSec (Λ i) (σ i) z) < -Real.exp (2 * a / c) :=
    (Real.log_lt_iff_lt_exp (hpos i)).2 hz
  have hri : Real.exp (2 * a / c) < rFun (Λ i) (σ i) z := by
    simp only [rFun, hlog i]
    linarith [Real.exp_pos 1]
  have hli : 2 * a / c < Real.log (rFun (Λ i) (σ i) z) :=
    (Real.lt_log_iff_exp_lt (hTpos.trans hri)).2 hri
  have hsum : Real.log (rFun (Λ i) (σ i) z) ≤ ∑ k, Real.log (rFun (Λ k) (σ k) z) :=
    Finset.single_le_sum (fun k _ => hnn k) (Finset.mem_univ i)
  have h2a : 2 * a < (∑ k, Real.log (rFun (Λ k) (σ k) z)) * c :=
    (div_lt_iff₀ hc0).1 (hli.trans_le hsum)
  simp only [pFun] at hza
  nlinarith

end GlobalTheory.PFunBoundary
