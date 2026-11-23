import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExphOnEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenClosureSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IteratedDerivChartTrans
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernReg.ExphOn

open Set

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ}

theorem dtrans_smul_real (c c' : AlgChart p σ d) (y : CxPts p σ) (t : ℝ) (v : Fin d → ℂ) :
    c.dtrans c' y (t • v) = t • c.dtrans c' y v := by
  funext b
  simp only [AlgChart.dtrans, Pi.smul_apply]
  rw [show WithLp.toLp 2 (t • v) = t • WithLp.toLp 2 v from rfl, ContinuousLinearMap.map_smul_of_tower]
  rfl

theorem form_zero_lt {R : AnRead p σ d} {a : ChartForm p σ d} (ha : IsKaehlerForm R a) {c : AlgChart p σ d}
    {y : CxPts p σ} (hy : y ∈ c.e.source) {ε : ℝ} (hε : 0 < ε) : a c y 0 < ε := by
  have h := (continuous_and_smul ha hy).2 0 0
  simp only [smul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at h
  rw [h]
  exact hε

theorem continuousAt_line {R : AnRead p σ d} {a : ChartForm p σ d} (ha : IsKaehlerForm R a) {E : ChartMap p σ d}
    {W : Set (CxPts p σ)} {ε : ℝ} (hε : 0 < ε) (hE : IsExphOn a E W ε) (c : AlgChart p σ d) {y : CxPts p σ}
    (hy : y ∈ c.e.source) (hW : y ∈ W) (ξ : ReciprocityTheory.L2DbarEstimates.V d) :
    ContinuousAt (fun t : ℝ => E c y (t • ξ.ofLp)) 0 := by
  have h := hE.cont c (c.e y) (c.e.map_source hy) (by rwa [c.e.left_inv hy]) 0
    (by rw [c.e.left_inv hy, WithLp.ofLp_zero]; exact form_zero_lt ha hy hε)
  have hl : ContinuousAt (fun t : ℝ => (c.e y, t • ξ)) 0 := by fun_prop
  have := h.comp_of_eq hl (by simp)
  convert this using 1
  funext t
  simp only [Function.comp_apply, c.e.left_inv hy]
  rfl

theorem contDiffAt_line {R : AnRead p σ d} {a : ChartForm p σ d} (ha : IsKaehlerForm R a) {E : ChartMap p σ d}
    {W : Set (CxPts p σ)} {ε : ℝ} (hε : 0 < ε) (hE : IsExphOn a E W ε) (c : AlgChart p σ d) {y : CxPts p σ}
    (hy : y ∈ c.e.source) (hW : y ∈ W) (η : Fin d → ℂ) :
    ContDiffAt ℝ ∞ (fun t : ℝ => c.e (E c y (t • η))) 0 := by
  have h := hE.smooth c c (c.e y) (c.e.map_source hy) (by rwa [c.e.left_inv hy]) 0
    (by rw [c.e.left_inv hy, WithLp.ofLp_zero]; exact form_zero_lt ha hy hε)
    (by rw [c.e.left_inv hy, WithLp.ofLp_zero, hE.zero c y hy hW]; exact hy)
  have hl : ContDiffAt ℝ ∞ (fun t : ℝ => (c.e y, t • WithLp.toLp 2 η)) 0 := by fun_prop
  have e0 : ((c.e y, (0 : ℝ) • WithLp.toLp 2 η) : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d) = (c.e y, 0) := by simp
  rw [← e0] at h
  have := h.comp (0 : ℝ) hl
  convert this using 1
  funext t
  simp only [Function.comp_apply, c.e.left_inv hy]
  rfl

theorem glue_jets : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) (R : AnRead p σ d) (a : ChartForm p σ d), IsKaehlerForm R a → ∀ (c : AlgChart p σ d) (E E' : ChartMap p σ d) (ρ : CxPts p σ → ℝ) (W W' W₀ O₁ : Set (CxPts p σ)) (ε ε' : ℝ), 0 < ε → 0 < ε' → ExphOn.IsExphOn a E W ε → ExphOn.IsExphOn a E' W' ε' → W₀ ⊆ W → O₁ ⊆ W' → (∀ y ∈ O₁, ρ y = 1) → (∀ y, ρ y ≠ 0 → y ∈ W') → W' ⊆ c.e.source → ∀ c₀ : AlgChart p σ d, ∀ y ∈ c₀.e.source, y ∈ W₀ ∪ O₁ → ∀ (ξ : ReciprocityTheory.L2DbarEstimates.V d) (n : ℕ), iteratedDeriv n (fun t : ℝ => c₀.e (ExphOn.glue c ρ E E' c₀ y (t • ξ.ofLp))) 0 = jet (matIn a c₀) n (c₀.e y, ξ) := by
  intro k _ Y p σ d R a ha c E E' ρ W W' W₀ O₁ ε ε' hε hε' hE hE' hW₀ hO₁W' hO₁ hρ hW' c₀ y hy hy0 ξ n
  by_cases h0 : ρ y = 0
  · have hyW : y ∈ W := by
      rcases hy0 with h | h
      · exact hW₀ h
      · exact absurd (hO₁ y h) (by rw [h0]; exact zero_ne_one)
    have e : (fun t : ℝ => c₀.e (glue c ρ E E' c₀ y (t • ξ.ofLp))) = fun t => c₀.e (E c₀ y (t • ξ.ofLp)) := by
      funext t
      simp only [glue]
      rw [if_pos h0]
    rw [e]
    exact hE.jets c₀ y hy hyW ξ n
  by_cases h1 : y ∈ O₁
  · have hyW' : y ∈ W' := hρ y h0
    have hcont := continuousAt_line ha hε' hE' c₀ hy hyW' ξ
    have hval : E' c₀ y ((0 : ℝ) • ξ.ofLp) = y := by rw [zero_smul]; exact hE'.zero c₀ y hy hyW'
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), E' c₀ y (t • ξ.ofLp) ∈ c.e.source :=
      hcont.preimage_mem_nhds (by rw [hval]; exact c.e.open_source.mem_nhds (hW' hyW'))
    have e : (fun t : ℝ => c₀.e (glue c ρ E E' c₀ y (t • ξ.ofLp))) =ᶠ[𝓝 0]
        fun t => c₀.e (E' c₀ y (t • ξ.ofLp)) := by
      filter_upwards [hev] with t ht
      simp only [glue]
      rw [if_neg h0, hO₁ y h1, sub_self, zero_smul, zero_add, one_smul, c.e.left_inv ht]
    rw [e.iteratedDeriv_eq n]
    exact hE'.jets c₀ y hy hyW' ξ n
  · have hyW : y ∈ W := hW₀ (hy0.resolve_right h1)
    have hyW' : y ∈ W' := hρ y h0
    have hyc : y ∈ c.e.source := hW' hyW'
    set η := c₀.dtrans c y ξ.ofLp with hη
    have hEt : ∀ t : ℝ, E c₀ y (t • ξ.ofLp) = E c y (t • η) := fun t => by
      rw [hE.trans c₀ c y hy hyc, dtrans_smul_real]
    have hE't : ∀ t : ℝ, E' c₀ y (t • ξ.ofLp) = E' c y (t • η) := fun t => by
      rw [hE'.trans c₀ c y hy hyc, dtrans_smul_real]
    set f : ℝ → ReciprocityTheory.L2DbarEstimates.V d := fun t => c.e (E c y (t • η)) with hfd
    set g : ℝ → ReciprocityTheory.L2DbarEstimates.V d := fun t => c.e (E' c y (t • η)) with hgd
    have hf : ContDiffAt ℝ ∞ f 0 := contDiffAt_line ha hε hE c hyc hyW η
    have hg : ContDiffAt ℝ ∞ g 0 := contDiffAt_line ha hε' hE' c hyc hyW' η
    set u : ℝ → CxPts p σ := fun t => glue c ρ E E' c₀ y (t • ξ.ofLp) with hud
    have hu : ∀ t, u t = c.e.symm ((1 - ρ y) • f t + ρ y • g t) := fun t => by
      simp only [hud, glue]
      rw [if_neg h0, hEt, hE't]
    have hcomb : ContDiffAt ℝ ∞ (fun t => (1 - ρ y) • f t + ρ y • g t) 0 :=
      (hf.const_smul _).add (hg.const_smul _)
    have hc0 : (1 - ρ y) • f 0 + ρ y • g 0 = c.e y := by
      simp only [hfd, hgd, zero_smul, hE.zero c y hyc hyW, hE'.zero c y hyc hyW']
      rw [← add_smul, sub_add_cancel, one_smul]
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), (1 - ρ y) • f t + ρ y • g t ∈ c.e.target :=
      hcomb.continuousAt.preimage_mem_nhds (by rw [hc0]; exact c.e.open_target.mem_nhds (c.e.map_source hyc))
    have hcu : (fun t => c.e (u t)) =ᶠ[𝓝 0] fun t => (1 - ρ y) • f t + ρ y • g t := by
      filter_upwards [hev] with t ht
      rw [hu, c.e.right_inv ht]
    have hu0 : u 0 = y := by rw [hu, hc0, c.e.left_inv hyc]
    have hucont : ContinuousAt u 0 := by
      have hs : ContinuousAt c.e.symm ((1 - ρ y) • f 0 + ρ y • g 0) := by
        rw [hc0]; exact c.e.continuousAt_symm (c.e.map_source hyc)
      have := hs.comp (x := (0 : ℝ)) hcomb.continuousAt
      convert this using 1
      funext t
      exact hu t
    have hjc : ∀ m : ℕ, iteratedDeriv m (fun t => c.e (u t)) 0 =
        jet (matIn a c) m (c.e (u 0), WithLp.toLp 2 η) := by
      intro m
      have hm : ((m : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
      rw [hcu.iteratedDeriv_eq m, iteratedDeriv_fun_add ((hf.const_smul _).of_le hm) ((hg.const_smul _).of_le hm),
        iteratedDeriv_fun_const_smul_field, iteratedDeriv_fun_const_smul_field, hu0]
      have j1 := hE.jets c y hyc hyW (WithLp.toLp 2 η) m
      have j2 := hE'.jets c y hyc hyW' (WithLp.toLp 2 η) m
      rw [hfd, hgd]
      simp only [WithLp.ofLp_toLp] at j1 j2
      rw [j1, j2, ← add_smul, sub_add_cancel, one_smul]
    have key := GlobalTheory.ChernReg.ExphOn.iteratedDeriv_chart_trans k Y p σ d R a ha c c₀ u (WithLp.toLp 2 η) (hu0 ▸ hyc) (hu0 ▸ hy) hucont
      (hcomb.congr_of_eventuallyEq hcu) hjc n
    rw [hu0] at key
    simp only [WithLp.ofLp_toLp] at key
    rw [hη, dtrans_dtrans c₀ c c₀ hy hyc hy, dtrans_self c₀ hy, WithLp.toLp_ofLp] at key
    exact key

end GlobalTheory.ChernReg.ExphOn
