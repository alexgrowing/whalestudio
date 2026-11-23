import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticLogResolution
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormLogPotentialFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormBoundedByPositivePotential

open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt Filter Topology
open scoped ENNReal ContDiff

namespace GlobalTheory.PoincareLevi

noncomputable section

theorem rFun_chart {d : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas d X} {L : LocPot X}
    {s : X → X → ℂ} (hL : IsPotential A L) (hs : IsSection A L s) (j : Fin A.n)
    {y : Fin d → ℂ} (hy : y ∈ (A.chart j).target)
    (hb : s ((A.chart j).symm y) ((A.chart j).symm y) ≠ 0) (w : Fin d → ℂ) :
    ContDiffAt ℝ 2 (rFun L s ∘ (A.chart j).symm) y ∧
      levi (rFun L s ∘ (A.chart j).symm) y w =
        2 * levi (L.φ ((A.chart j).symm y) ∘ (A.chart j).symm) y w := by
  have hyU : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U ((A.chart j).symm y) :=
    ⟨hy, L.mem_U _⟩
  have hga : AnalyticAt ℂ (s ((A.chart j).symm y) ∘ (A.chart j).symm) y := hs.1 _ j y hyU
  have hgy : (s ((A.chart j).symm y) ∘ (A.chart j).symm) y ≠ 0 := hb
  have hGa : AnalyticAt ℂ (fun u => Complex.log ((s ((A.chart j).symm y) ∘ (A.chart j).symm) u /
      (s ((A.chart j).symm y) ∘ (A.chart j).symm) y)) y := by
    refine (hga.div analyticAt_const hgy).clog ?_
    simp only [Pi.div_apply]
    rw [div_self hgy]
    exact Complex.one_mem_slitPlane
  have hRe : ContDiffAt ℝ 2 (fun u => (Complex.log ((s ((A.chart j).symm y) ∘ (A.chart j).symm) u /
      (s ((A.chart j).symm y) ∘ (A.chart j).symm) y)).re) y := by
    have := (Complex.reCLM.contDiff (n := 2)).contDiffAt.comp y
      (hGa.restrictScalars (𝕜 := ℝ)).contDiffAt
    simpa [Function.comp_def] using this
  have hφ : ContDiffAt ℝ 2 (L.φ ((A.chart j).symm y) ∘ (A.chart j).symm) y :=
    GlobalTheory.ChernCompare.pot_contDiffAt hL (GlobalTheory.ChernCompare.compat_self A j) _ hy (L.mem_U _)
  have hf0 : ContDiffAt ℝ 2 (fun u => (Real.exp 1 - 2 * Real.log ‖s ((A.chart j).symm y) ((A.chart j).symm y)‖)
      + (-2) * (Complex.log ((s ((A.chart j).symm y) ∘ (A.chart j).symm) u /
      (s ((A.chart j).symm y) ∘ (A.chart j).symm) y)).re) y :=
    contDiffAt_const.add (contDiffAt_const.mul hRe)
  have hev : (rFun L s ∘ (A.chart j).symm) =ᶠ[𝓝 y]
      fun u => ((Real.exp 1 - 2 * Real.log ‖s ((A.chart j).symm y) ((A.chart j).symm y)‖)
        + (-2) * (Complex.log ((s ((A.chart j).symm y) ∘ (A.chart j).symm) u /
        (s ((A.chart j).symm y) ∘ (A.chart j).symm) y)).re) +
        2 * (L.φ ((A.chart j).symm y) ∘ (A.chart j).symm) u := by
    have h1 : ∀ᶠ u in 𝓝 y, u ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U ((A.chart j).symm y) :=
      ((A.chart j).isOpen_inter_preimage_symm (L.isOpen_U _)).mem_nhds hyU
    have h2 : ∀ᶠ u in 𝓝 y, (s ((A.chart j).symm y) ∘ (A.chart j).symm) u ≠ 0 :=
      hga.continuousAt.eventually_ne hgy
    filter_upwards [h1, h2] with u hu hu0
    have hsec := hs.2 ((A.chart j).symm u) ((A.chart j).symm y) ((A.chart j).symm u) ⟨L.mem_U _, hu.2⟩
    simp only [Function.comp_apply] at hu0 hgy ⊢
    simp only [rFun, logNormSec]
    rw [hsec]
    have hgu : ‖s ((A.chart j).symm y) ((A.chart j).symm u)‖ ≠ 0 := norm_ne_zero_iff.2 hu0
    rw [Real.log_mul hgu (Real.exp_pos _).ne', Real.log_exp, Complex.log_re, norm_div,
      Real.log_div hgu (norm_ne_zero_iff.2 hgy)]
    ring
  refine ⟨(hf0.add (contDiffAt_const.mul hφ)).congr_of_eventuallyEq hev, ?_⟩
  rw [levi_congr hev, levi_add_smul 2 hf0 hφ w,
    levi_add_smul (f := fun _ => Real.exp 1 - 2 * Real.log ‖s ((A.chart j).symm y) ((A.chart j).symm y)‖)
      (-2) contDiffAt_const hRe w, levi_re_analytic hGa w]
  simp [levi]

theorem levi_nonneg : ∀ (d : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas d X) (m : ℕ)
    (α : LocPot X) (Λ : Fin m → LocPot X) (σ : Fin m → X → X → ℂ) (c : ℝ),
    IsBoundarySetting A α Λ σ c →
    ∀ (x : X) (j : Fin A.n), ∀ y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (α.U x ∩ (boundary σ)ᶜ),
      ∀ w : Fin d → ℂ, 0 ≤ levi ((fun z => α.φ x z + pFun Λ σ c z / 2) ∘ (A.chart j).symm) y w := by
  intro d X _ A m α Λ σ c hB x j y hy w
  obtain ⟨hαP, hαpos, hΛ, hc0, K, hK, hcK⟩ := hB
  have hyt : y ∈ (A.chart j).target := hy.1
  have hbx : (A.chart j).symm y ∈ α.U x := hy.2.1
  have hσb : ∀ i, σ i ((A.chart j).symm y) ((A.chart j).symm y) ≠ 0 :=
    fun i h => hy.2.2 ⟨i, h⟩
  have hloc := fun i => rFun_chart (hΛ i).1 (hΛ i).2.1 j hyt (hσb i) w
  have he : 0 < Real.exp 1 := Real.exp_pos 1

  have hr : ∀ i, Real.exp 1 ≤ (rFun (Λ i) (σ i) ∘ (A.chart j).symm) y := by
    intro i
    have h1 := (hΛ i).2.2.2 ((A.chart j).symm y)
    simp only [normSec] at h1
    have h0 : 0 ≤ ‖σ i ((A.chart j).symm y) ((A.chart j).symm y)‖ *
        Real.exp (-(Λ i).φ ((A.chart j).symm y) ((A.chart j).symm y)) := by positivity
    have := Real.log_nonpos h0 h1
    simp only [Function.comp_apply, rFun, logNormSec]
    linarith
  have hrpos : ∀ i, 0 < (rFun (Λ i) (σ i) ∘ (A.chart j).symm) y := fun i => he.trans_le (hr i)

  have hα : ContDiffAt ℝ 2 (α.φ x ∘ (A.chart j).symm) y :=
    GlobalTheory.ChernCompare.pot_contDiffAt hαP (GlobalTheory.ChernCompare.compat_self A j) x hyt hbx
  have hLa : 0 ≤ levi (α.φ x ∘ (A.chart j).symm) y w := by
    rcases eq_or_ne w 0 with rfl | hw
    · rw [levi_zero]
    · exact (hαpos x j y ⟨hyt, hbx⟩ w hw).le
  have hαb : levi (α.φ ((A.chart j).symm y) ∘ (A.chart j).symm) y w =
      levi (α.φ x ∘ (A.chart j).symm) y w :=
    GlobalTheory.ChernCompare.levi_base_compat hαP (GlobalTheory.ChernCompare.compat_self A j) x hyt hbx w

  have hbd : ∀ i, levi ((Λ i).φ ((A.chart j).symm y) ∘ (A.chart j).symm) y w ≤
      K i * levi (α.φ x ∘ (A.chart j).symm) y w := by
    intro i
    have hαb' : ContDiffAt ℝ 2 (α.φ ((A.chart j).symm y) ∘ (A.chart j).symm) y :=
      GlobalTheory.ChernCompare.pot_contDiffAt hαP (GlobalTheory.ChernCompare.compat_self A j) _ hyt (α.mem_U _)
    have hΛb : ContDiffAt ℝ 2 ((Λ i).φ ((A.chart j).symm y) ∘ (A.chart j).symm) y :=
      GlobalTheory.ChernCompare.pot_contDiffAt (hΛ i).1 (GlobalTheory.ChernCompare.compat_self A j) _ hyt
        ((Λ i).mem_U _)
    have hmem : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹'
        (α.rsmul (K i) + Λ i).U ((A.chart j).symm y) := by
      refine ⟨hyt, ?_⟩
      show (A.chart j).symm y ∈ α.U ((A.chart j).symm y) ∩ (Λ i).U ((A.chart j).symm y)
      exact ⟨α.mem_U _, (Λ i).mem_U _⟩
    have hmem' : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹'
        (α.rsmul (K i) + (Λ i).rsmul (-1)).U ((A.chart j).symm y) := by
      refine ⟨hyt, ?_⟩
      show (A.chart j).symm y ∈ α.U ((A.chart j).symm y) ∩ (Λ i).U ((A.chart j).symm y)
      exact ⟨α.mem_U _, (Λ i).mem_U _⟩
    have h1 := (hK i).2.2 ((A.chart j).symm y) j y hmem' w
    have e1 : ((α.rsmul (K i) + (Λ i).rsmul (-1)).φ ((A.chart j).symm y) ∘ (A.chart j).symm) =
        fun u => K i * (α.φ ((A.chart j).symm y) ∘ (A.chart j).symm) u +
          (-1) * ((Λ i).φ ((A.chart j).symm y) ∘ (A.chart j).symm) u := by
      funext u; rfl
    rw [e1, GlobalTheory.LeviLogChain.levi_add_of (contDiffAt_const.mul hαb') (contDiffAt_const.mul hΛb) w,
      GlobalTheory.LeviLogChain.levi_const_mul_of _ hαb' w, GlobalTheory.LeviLogChain.levi_const_mul_of _ hΛb w,
      hαb] at h1
    linarith

  have hlog : ∀ i, ContDiffAt ℝ 2
      (fun u => Real.log ((rFun (Λ i) (σ i) ∘ (A.chart j).symm) u)) y :=
    fun i => (hloc i).1.log (hrpos i).ne'
  have hS := GlobalTheory.LeviLogChain.levi_sum_of
    (fun i u => Real.log ((rFun (Λ i) (σ i) ∘ (A.chart j).symm) u)) hlog w Finset.univ
  have eF : ((fun z => α.φ x z + pFun Λ σ c z / 2) ∘ (A.chart j).symm) =
      fun u => (α.φ x ∘ (A.chart j).symm) u + -(c / 2) *
        ∑ i, Real.log ((rFun (Λ i) (σ i) ∘ (A.chart j).symm) u) := by
    funext u
    simp only [Function.comp_apply, pFun]
    ring
  rw [eF, GlobalTheory.LeviLogChain.levi_add_of hα (contDiffAt_const.mul hS.1) w,
    GlobalTheory.LeviLogChain.levi_const_mul_of _ hS.1 w, hS.2]
  simp only [GlobalTheory.LeviLogChain.levi_log (hloc _).1 (hrpos _) w, (hloc _).2]

  set La := levi (α.φ x ∘ (A.chart j).symm) y w with hLadef
  have hterm : ∀ i, 2 * levi ((Λ i).φ ((A.chart j).symm y) ∘ (A.chart j).symm) y w /
        (rFun (Λ i) (σ i) ∘ (A.chart j).symm) y -
      ((fderiv ℝ (rFun (Λ i) (σ i) ∘ (A.chart j).symm) y w ^ 2 +
        fderiv ℝ (rFun (Λ i) (σ i) ∘ (A.chart j).symm) y (Complex.I • w) ^ 2) / 4) /
        (rFun (Λ i) (σ i) ∘ (A.chart j).symm) y ^ 2 ≤ 2 * K i * La / Real.exp 1 := by
    intro i
    have hq : 0 ≤ ((fderiv ℝ (rFun (Λ i) (σ i) ∘ (A.chart j).symm) y w ^ 2 +
        fderiv ℝ (rFun (Λ i) (σ i) ∘ (A.chart j).symm) y (Complex.I • w) ^ 2) / 4) /
        (rFun (Λ i) (σ i) ∘ (A.chart j).symm) y ^ 2 := by positivity
    have hKL : 0 ≤ K i * La := mul_nonneg (hK i).1 hLa
    have a1 : 2 * levi ((Λ i).φ ((A.chart j).symm y) ∘ (A.chart j).symm) y w /
        (rFun (Λ i) (σ i) ∘ (A.chart j).symm) y ≤
        2 * K i * La / (rFun (Λ i) (σ i) ∘ (A.chart j).symm) y := by
      apply div_le_div_of_nonneg_right _ (hrpos i).le
      have := hbd i
      linarith
    have a2 : 2 * K i * La / (rFun (Λ i) (σ i) ∘ (A.chart j).symm) y ≤ 2 * K i * La / Real.exp 1 :=
      div_le_div_of_nonneg_left (by linarith) he (hr i)
    linarith
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
  rw [← Finset.sum_div, ← Finset.sum_mul, ← Finset.mul_sum] at hsum
  have hcS : c * (2 * (∑ i, K i) * La / Real.exp 1) ≤ La := by
    rw [mul_div_assoc', div_le_iff₀ he]
    nlinarith
  nlinarith

end

end GlobalTheory.PoincareLevi
