import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialSmoothInChart
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff

namespace GlobalTheory.LeviChern

theorem levi_const_add {ι : Type} [Fintype ι] (c : ℝ) (f : (ι → ℂ) → ℝ) (z w : ι → ℂ) :
    levi (fun x => c + f x) z w = levi f z w := by
  unfold levi
  have : fderiv ℝ (fun x => c + f x) = fderiv ℝ f := funext fun _ => fderiv_const_add _
  rw [this]

end GlobalTheory.LeviChern

namespace GlobalTheory.LeviChern

open Filter Topology

theorem ddcAt_rComp_eq_formAt : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {m : ℕ} (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ) (D : Fin m → Set X),
    IsBoundary A L s D → ∀ (i : Fin m) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)),
    IsCompatChart A ψ → ∀ z ∈ ψ.target, ψ.symm z ∉ D i → ∀ w,
    ddcAt ψ (rComp L s i) z w = formAt ψ (L i) z w := by
  intro e X _ A m L s D hB i ψ hψ z hz hD w
  obtain ⟨hpot, hsec, hsnc, -⟩ := hB i

  have hne : s i (ψ.symm z) (ψ.symm z) ≠ 0 := by
    obtain ⟨ψ', -, hy0src, -, σ, -, hDσ, u, -, hu0, hs⟩ := hsnc (ψ.symm z)
    rw [hs _ hy0src]
    refine mul_ne_zero (hu0 _ hy0src) ?_
    rw [Finset.prod_ne_zero_iff]
    intro k _
    rcases hk : σ k with _ | j
    · simp
    · simp only
      by_cases hki : k = i
      · subst hki
        simp only [Pi.single_eq_same, pow_one]
        intro h0
        apply hD
        have : ψ.symm z ∈ D k ∩ ψ'.source := by
          rw [hDσ k]
          exact ⟨hy0src, j, hk, h0⟩
        exact this.1
      · simp [Pi.single_eq_of_ne hki]

  obtain ⟨j, hj⟩ := A.cover (ψ.symm z)
  have hG : AnalyticAt ℂ (A.chart j ∘ ψ.symm) z := (hψ j).2 z ⟨hz, hj⟩
  have hF : AnalyticAt ℂ (s i (ψ.symm z) ∘ (A.chart j).symm) (A.chart j (ψ.symm z)) :=
    hsec.1 (ψ.symm z) j _ ⟨(A.chart j).map_source hj, by
      simp only [Set.mem_preimage, (A.chart j).left_inv hj]; exact (L i).mem_U _⟩
  have hsymm : ContinuousAt ψ.symm z := ψ.continuousAt_symm hz
  have hsrc : ∀ᶠ z' in 𝓝 z, ψ.symm z' ∈ (A.chart j).source :=
    hsymm.preimage_mem_nhds ((A.chart j).open_source.mem_nhds hj)
  have hh : AnalyticAt ℂ (fun z' => s i (ψ.symm z) (ψ.symm z')) z :=
    (AnalyticAt.comp (g := s i (ψ.symm z) ∘ (A.chart j).symm) (f := A.chart j ∘ ψ.symm) hF hG).congr (hsrc.mono fun z' hz' => by simp [(A.chart j).left_inv hz'])
  have hhz : s i (ψ.symm z) (ψ.symm z) ≠ 0 := hne

  have hHa : AnalyticAt ℂ
      (fun z' => Complex.log (s i (ψ.symm z) (ψ.symm z') / s i (ψ.symm z) (ψ.symm z))) z :=
    (hh.div analyticAt_const hhz).clog (by
      show s i (ψ.symm z) (ψ.symm z) / s i (ψ.symm z) (ψ.symm z) ∈ Complex.slitPlane
      rw [div_self hhz]
      exact Complex.one_mem_slitPlane)
  have hHC : ContDiffAt ℝ 2
      (fun z' => Complex.log (s i (ψ.symm z) (ψ.symm z') / s i (ψ.symm z) (ψ.symm z))) z :=
    (hHa.contDiffAt (n := 2)).restrict_scalars ℝ
  have hReC : ContDiffAt ℝ 2
      (fun z' => (Complex.log (s i (ψ.symm z) (ψ.symm z') / s i (ψ.symm z) (ψ.symm z))).re) z :=
    Complex.reCLM.contDiff.contDiffAt.comp z hHC
  have hφ : ContDiffAt ℝ 2 ((L i).φ (ψ.symm z) ∘ ψ.symm) z :=
    (GlobalTheory.isPotential_contDiffAt_compatChart A (L i) hpot ψ hψ z hz).of_le (show (2 : WithTop ℕ∞) ≤ ∞ by norm_cast)

  have hU : ∀ᶠ z' in 𝓝 z, ψ.symm z' ∈ (L i).U (ψ.symm z) :=
    hsymm.preimage_mem_nhds (((L i).isOpen_U _).mem_nhds ((L i).mem_U _))
  have hhne : ∀ᶠ z' in 𝓝 z, s i (ψ.symm z) (ψ.symm z') ≠ 0 := hh.continuousAt.eventually_ne hhz
  have key : rComp L s i ∘ ψ.symm =ᶠ[𝓝 z] fun z' =>
      (Real.exp 1 - 2 * Real.log ‖s i (ψ.symm z) (ψ.symm z)‖) +
        (2 * ((L i).φ (ψ.symm z) ∘ ψ.symm) z' +
          (-2) * (Complex.log (s i (ψ.symm z) (ψ.symm z') / s i (ψ.symm z) (ψ.symm z))).re) := by
    filter_upwards [hU, hhne] with z' hz'U hz'ne
    have hglue := hsec.2 (ψ.symm z') (ψ.symm z) (ψ.symm z') ⟨(L i).mem_U _, hz'U⟩
    have hHre : (Complex.log (s i (ψ.symm z) (ψ.symm z') / s i (ψ.symm z) (ψ.symm z))).re
        = Real.log ‖s i (ψ.symm z) (ψ.symm z')‖ - Real.log ‖s i (ψ.symm z) (ψ.symm z)‖ := by
      rw [Complex.log_re, norm_div,
        Real.log_div (norm_ne_zero_iff.2 hz'ne) (norm_ne_zero_iff.2 hhz)]
    simp only [Function.comp, rComp, normSec]
    rw [hglue, hHre, Real.log_pow,
      Real.log_mul (norm_ne_zero_iff.2 hz'ne) (Real.exp_pos _).ne', Real.log_exp]
    push_cast
    ring
  have h2 : levi (fun z' => 2 * ((L i).φ (ψ.symm z) ∘ ψ.symm) z') z w
      = 2 * levi ((L i).φ (ψ.symm z) ∘ ψ.symm) z w := by
    have := levi_add_smul 1 hφ hφ w
    rw [show (fun z' => 2 * ((L i).φ (ψ.symm z) ∘ ψ.symm) z') = fun z' =>
      ((L i).φ (ψ.symm z) ∘ ψ.symm) z' + 1 * ((L i).φ (ψ.symm z) ∘ ψ.symm) z' from
        funext fun _ => by ring, this]
    ring
  have h3 := levi_add_smul (f := fun z' => 2 * ((L i).φ (ψ.symm z) ∘ ψ.symm) z') (-2)
    ((contDiffAt_const (c := (2 : ℝ))).mul hφ) hReC w
  unfold ddcAt formAt
  rw [levi_congr key, levi_const_add, h3, levi_re_analytic hHa, h2]
  ring

end GlobalTheory.LeviChern
