import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsLocSec
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FubiniStudyMetricSmooth
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

private theorem isPotential_secPot_of_isSmoothHerm {κ : Type} [Fintype κ] {ρ : κ → Type} [∀ k, Fintype (ρ k)]
    {P J : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ρ)} {e : ℕ} (R : ReciprocityTheory.ChartRestriction.G.Geo.AnLogRes P J e)
    (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ρ) (hA : ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm A)
    (V : R.X → Set R.X) (hV : ∀ x, IsOpen (V x)) (hm : ∀ x, x ∈ V x) (hVU : ∀ x, V x ⊆ R.U x)
    (c : ℝ) : ReciprocityTheory.AnForm.M.IsPotential R.A (secPot R A V hV hm c) := by
  have hA' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := hA
  have hol : ∀ (x : R.X) (p : (k : κ) × ρ k) (j : Fin R.A.n) (t : Fin e → ℂ),
      t ∈ (R.A.chart j).target → (R.A.chart j).symm t ∈ R.U x →
      AnalyticAt ℂ (fun s => R.lift x ((R.A.chart j).symm s) p) t :=
    fun x p j t ht hu => R.holo x p j t ⟨ht, hu⟩
  have memNZ : ∀ (z0 y0 : R.X), y0 ∈ R.U z0 → ∀ k, ∃ i, R.lift z0 y0 ⟨k, i⟩ ≠ 0 := by
    intro z0 y0 h
    have h' := R.mem z0 y0 h
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.mcPts, Set.mem_ofPred_eq] at h'
    exact h'.1
  unfold ReciprocityTheory.AnForm.M.IsPotential ReciprocityTheory.AnForm.M.FinHolAtlas.SmoothOn
    ReciprocityTheory.AnForm.M.FinHolAtlas.HoloOn
  dsimp only [secPot]
  refine ⟨fun x j => ?_, fun x x' y hy => ?_⟩
  · have hlift : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => R.lift x ((R.A.chart j).symm t))
        ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' V x) := by
      rw [contDiffOn_pi]
      intro p
      have h1 : ContDiffOn ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => R.lift x ((R.A.chart j).symm t) p)
          ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' V x) :=
        fun t ht => (hol x p j t ht.1 (hVU x ht.2)).contDiffAt.contDiffWithinAt
      exact h1.restrict_scalars ℝ
    have hmem : ∀ t ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' V x,
        (∀ k, ∃ i, R.lift x ((R.A.chart j).symm t) ⟨k, i⟩ ≠ 0) :=
      fun t ht => memNZ x _ (hVU x ht.2)
    have hh := hA'.comp hlift (fun t ht => hmem t ht)
    have hne : ∀ t ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' V x,
        A.h (R.lift x ((R.A.chart j).symm t)) ≠ 0 :=
      fun t ht => (A.pos _ (hmem t ht)).ne'
    exact (hh.log hne).add contDiffOn_const
  · obtain ⟨hyx, hyx'⟩ := hy
    have hyU : y ∈ R.U x := hVU x hyx
    have hyU' : y ∈ R.U x' := hVU x' hyx'
    choose i hi using memNZ x' y hyU'
    obtain ⟨r, hr⟩ : ∃ r : κ → R.X → ℂ,
        ∀ k z, r k z = R.lift x z ⟨k, i k⟩ / R.lift x' z ⟨k, i k⟩ :=
      ⟨fun k z => R.lift x z ⟨k, i k⟩ / R.lift x' z ⟨k, i k⟩, fun _ _ => rfl⟩
    have hry : ∀ k, r k y ≠ 0 := by
      intro k
      obtain ⟨cy, hcy, hly⟩ := R.compat x x' y ⟨hyU, hyU'⟩
      have h1 := congrFun hly ⟨k, i k⟩
      rw [hr, h1]
      exact div_ne_zero (mul_ne_zero (hcy k) (hi k)) (hi k)
    obtain ⟨j, hj⟩ := R.A.cover y
    have hD : IsOpen ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' (R.U x ∩ R.U x')) :=
      (R.A.chart j).isOpen_inter_preimage_symm ((R.isOpen_U x).inter (R.isOpen_U x'))
    obtain ⟨O, hOdef⟩ : ∃ O : Set (Fin e → ℂ), O = {t | t ∈ (R.A.chart j).target ∧
        (R.A.chart j).symm t ∈ R.U x ∩ R.U x' ∧
        (∀ k, R.lift x' ((R.A.chart j).symm t) ⟨k, i k⟩ ≠ 0) ∧
        ∀ k, r k ((R.A.chart j).symm t) / r k y ∈ Complex.slitPlane} := ⟨_, rfl⟩
    have memO : ∀ t, t ∈ O ↔ (t ∈ (R.A.chart j).target ∧
        (R.A.chart j).symm t ∈ R.U x ∩ R.U x' ∧
        (∀ k, R.lift x' ((R.A.chart j).symm t) ⟨k, i k⟩ ≠ 0) ∧
        ∀ k, r k ((R.A.chart j).symm t) / r k y ∈ Complex.slitPlane) := by
      intro t; rw [hOdef]; rfl
    have hO : IsOpen O := by
      rw [isOpen_iff_mem_nhds]
      intro t ht
      obtain ⟨htT, htU, htne, htsl⟩ := (memO t).1 ht
      have hDn : (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' (R.U x ∩ R.U x') ∈ 𝓝 t :=
        hD.mem_nhds ⟨htT, htU⟩
      have hca : ∀ (z0 : R.X) (p : (k : κ) × ρ k), (R.A.chart j).symm t ∈ R.U z0 →
          ContinuousAt (fun s => R.lift z0 ((R.A.chart j).symm s) p) t :=
        fun z0 p hz => (hol z0 p j t htT hz).continuousAt
      have e1 : ∀ᶠ s in 𝓝 t, ∀ k, R.lift x' ((R.A.chart j).symm s) ⟨k, i k⟩ ≠ 0 := by
        rw [Filter.eventually_all]
        intro k
        exact (hca x' _ htU.2).eventually_ne (htne k)
      have e2 : ∀ᶠ s in 𝓝 t, ∀ k, r k ((R.A.chart j).symm s) / r k y ∈ Complex.slitPlane := by
        rw [Filter.eventually_all]
        intro k
        have hc0 : ContinuousAt (fun s => r k ((R.A.chart j).symm s)) t := by
          simp only [hr]
          exact (hca x _ htU.1).div (hca x' _ htU.2) (htne k)
        have hc : ContinuousAt (fun s => r k ((R.A.chart j).symm s) / r k y) t :=
          hc0.div_const _
        exact hc.preimage_mem_nhds (Complex.isOpen_slitPlane.mem_nhds (htsl k))
      filter_upwards [hDn, e1, e2] with s hs1 hs2 hs3
      exact (memO s).2 ⟨hs1.1, hs1.2, hs2, hs3⟩
    have hWopen : IsOpen ((R.A.chart j).source ∩ (R.A.chart j) ⁻¹' O) :=
      (R.A.chart j).isOpen_inter_preimage hO
    have hsy : (R.A.chart j).symm ((R.A.chart j) y) = y := (R.A.chart j).left_inv hj
    have hyW : y ∈ (R.A.chart j).source ∩ (R.A.chart j) ⁻¹' O := by
      refine ⟨hj, (memO _).2 ?_⟩
      rw [hsy]
      refine ⟨(R.A.chart j).map_source hj, ⟨hyU, hyU'⟩, hi, fun k => ?_⟩
      rw [div_self (hry k)]
      exact Complex.one_mem_slitPlane
    have condW : ∀ z ∈ (R.A.chart j).source ∩ (R.A.chart j) ⁻¹' O, z ∈ R.U x ∧ z ∈ R.U x' ∧
        (∀ k, R.lift x' z ⟨k, i k⟩ ≠ 0) ∧ ∀ k, r k z / r k y ∈ Complex.slitPlane := by
      intro z hz
      have h2 := (memO ((R.A.chart j) z)).1 hz.2
      rw [(R.A.chart j).left_inv hz.1] at h2
      exact ⟨h2.2.1.1, h2.2.1.2, h2.2.2.1, h2.2.2.2⟩
    refine ⟨(R.A.chart j).source ∩ (R.A.chart j) ⁻¹' O, hWopen, hyW,
      fun z => (∑ k, ((A.a k : ℝ) : ℂ) * Complex.log (r k z / r k y)) +
        ((∑ k, (A.a k : ℝ) * Real.log ‖r k y‖ : ℝ) : ℂ), ?_, ?_⟩
    · intro j' t ht
      obtain ⟨hUx, hUx', hne, hsl⟩ := condW _ ht.2
      have hra : ∀ k, AnalyticAt ℂ (fun s => r k ((R.A.chart j').symm s)) t := by
        intro k
        simp only [hr]
        exact (hol x _ j' t ht.1 hUx).div (hol x' _ j' t ht.1 hUx') (hne k)
      show AnalyticAt ℂ (fun s => (∑ k, ((A.a k : ℝ) : ℂ) *
          Complex.log (r k ((R.A.chart j').symm s) / r k y)) +
        ((∑ k, (A.a k : ℝ) * Real.log ‖r k y‖ : ℝ) : ℂ)) t
      refine AnalyticAt.add ?_ analyticAt_const
      have hs : ∀ k ∈ (Finset.univ : Finset κ), AnalyticAt ℂ (fun s => ((A.a k : ℝ) : ℂ) *
          Complex.log (r k ((R.A.chart j').symm s) / r k y)) t :=
        fun k _ => analyticAt_const.mul (((hra k).div analyticAt_const (hry k)).clog (hsl k))
      have h3 := Finset.analyticAt_sum Finset.univ hs
      rw [Finset.sum_fn] at h3
      exact h3
    · intro z hz
      obtain ⟨hUx, hUx', hne, -⟩ := condW z hz.1.1
      obtain ⟨cz, hcz, hlz⟩ := R.compat x x' z ⟨hUx, hUx'⟩
      have hrz : ∀ k, r k z = cz k := by
        intro k
        rw [hr]
        have h1 := congrFun hlz ⟨k, i k⟩
        rw [h1]
        exact mul_div_cancel_right₀ _ (hne k)
      have hhz : A.h (R.lift x z) = (∏ k, ‖cz k‖ ^ A.a k) * A.h (R.lift x' z) := by
        rw [hlz]; exact A.smul cz _ hcz
      have hhpos : 0 < A.h (R.lift x' z) := A.pos _ (memNZ x' z hUx')
      have hczn : ∀ k, ‖cz k‖ ≠ 0 := fun k => norm_ne_zero_iff.2 (hcz k)
      have hryn : ∀ k, ‖r k y‖ ≠ 0 := fun k => norm_ne_zero_iff.2 (hry k)
      have lhs : (Real.log (A.h (R.lift x z)) + c) - (Real.log (A.h (R.lift x' z)) + c) =
          ∑ k, (A.a k : ℝ) * Real.log ‖cz k‖ := by
        rw [hhz, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hczn k))
          hhpos.ne', Real.log_prod (fun k _ => zpow_ne_zero _ (hczn k))]
        simp only [Real.log_zpow]
        ring
      show (Real.log (A.h (R.lift x z)) + c) - (Real.log (A.h (R.lift x' z)) + c) =
        ((∑ k, ((A.a k : ℝ) : ℂ) * Complex.log (r k z / r k y)) +
          ((∑ k, (A.a k : ℝ) * Real.log ‖r k y‖ : ℝ) : ℂ)).re
      rw [lhs]
      simp only [Complex.add_re, Complex.re_sum, Complex.re_ofReal_mul, Complex.ofReal_re,
        Complex.log_re, norm_div, hrz]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Real.log_div (hczn k) (hryn k)]
      ring

theorem isPotential_secPot : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (ψ : RW.X → OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : RW.X → Fin Rb.A.n) (σ : RW.X → Fin n ↪ Fin e) (i₀ : RW.X → Fin e) (V : RW.X → Set RW.X) (u : RW.X → RW.X → ℂ) (hL : ∀ x, IsLocSec M Rb τ a k₀ ca cb RW pr x (ψ x) (kb x) (σ x) (i₀ x) (V x) (u x)), ∀ c : ℝ, IsPotential RW.A (secPot RW (potA M τ a k₀) V (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL c
  have hS : ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm (potA M τ a k₀) := by
    unfold GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.potA
    exact GlobalTheory.CompanionTheory.Ar.PB.StepW.fsHerm_isSmoothHerm _ _ _
  exact isPotential_secPot_of_isSmoothHerm RW (potA M τ a k₀) hS V _ _ (fun x => (hL x).2.2.2.2.1) c

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
