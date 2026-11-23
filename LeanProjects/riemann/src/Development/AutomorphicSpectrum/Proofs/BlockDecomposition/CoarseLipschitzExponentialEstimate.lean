import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
open Filter Topology

namespace GlobalTheory.CompanionTheory.EisCross

open PositivityTheory.RgEis

theorem pos_nonneg' {G : Type} [Group G] (Δ P : Subgroup G) (l : G → ℝ) (g : G) : 0 ≤ pos Δ P l g := by
  unfold pos
  exact tsum_nonneg fun _ => (Real.exp_pos _).le

theorem pos_mul_le {G : Type} [Group G] (Δ P : Subgroup G) (l : G → ℝ) (C : Set G) (A : ℝ)
    (hA : ∀ g, ∀ u ∈ C, |l (g * u) - l g| ≤ A) (hc : Conv Δ P l) (y v : G) (hv : v ∈ C) :
    pos Δ P l (y * v) ≤ Real.exp A * pos Δ P l y := by
  unfold pos
  have hle : ∀ q : Cos P Δ, Real.exp (l (rep q * (y * v))) ≤ Real.exp A * Real.exp (l (rep q * y)) := by
    intro q
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := hA (rep q * y) v hv
    rw [mul_assoc] at h
    have h' := (abs_le.mp h).2
    linarith
  have hs : Summable fun q : Cos P Δ => Real.exp A * Real.exp (l (rep q * y)) := (hc y).mul_left _
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) hle hs) hs

theorem exp_between (e₁ e₂ t s : ℝ) (h₁ : e₁ ≤ t) (h₂ : t ≤ e₂) :
    Real.exp (t * s) ≤ Real.exp (e₁ * s) + Real.exp (e₂ * s) := by
  rcases le_total 0 s with hs | hs
  · have h3 : t * s ≤ e₂ * s := mul_le_mul_of_nonneg_right h₂ hs
    have h4 := Real.exp_le_exp.mpr h3
    have h5 := Real.exp_pos (e₁ * s)
    linarith
  · have h3 : t * s ≤ e₁ * s := mul_le_mul_of_nonpos_right h₁ hs
    have h4 := Real.exp_le_exp.mpr h3
    have h5 := Real.exp_pos (e₂ * s)
    linarith

theorem exp_shift (e a b A : ℝ) (h : |a - b| ≤ A) :
    Real.exp (e * a) ≤ Real.exp (|e| * A) * Real.exp (e * b) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : e * (a - b) ≤ |e| * |a - b| := by
    rw [← abs_mul]
    exact le_abs_self _
  have h2 : |e| * |a - b| ≤ |e| * A := mul_le_mul_of_nonneg_left h (abs_nonneg e)
  have h3 : e * (a - b) = e * a - e * b := by ring
  linarith

theorem dom : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (Γ Δ P P' : Subgroup G) (ξ l₁ l₂ : G → ℝ) (H : ℂ → G → X)
    (a b e₁ e₂ M : ℝ),
    (∀ C : Set G, IsCompact C → ∃ A : ℝ, ∀ g, ∀ u ∈ C, |ξ (g * u) - ξ g| ≤ A) →
    (∀ C : Set G, IsCompact C → ∃ A : ℝ, ∀ g, ∀ u ∈ C, |l₁ (g * u) - l₁ g| ≤ A) →
    (∀ C : Set G, IsCompact C → ∃ A : ℝ, ∀ g, ∀ u ∈ C, |l₂ (g * u) - l₂ g| ≤ A) →
    PositivityTheory.RgEis.Conv Δ P l₁ → PositivityTheory.RgEis.Conv Δ P' l₂ →
    (∀ z : ℂ, b ≤ z.re → z.re ≤ a → ∀ g, ‖H z g‖ ≤ M * (PositivityTheory.RgEis.pos Δ P l₁ g + PositivityTheory.RgEis.pos Δ P' l₂ g)) →
    (∀ g, Summable fun r : PositivityTheory.RgEis.Cos Δ Γ => Real.exp (e₁ * ξ (PositivityTheory.RgEis.rep r * g)) *
      PositivityTheory.RgEis.pos Δ P l₁ (PositivityTheory.RgEis.rep r * g)) →
    (∀ g, Summable fun r : PositivityTheory.RgEis.Cos Δ Γ => Real.exp (e₂ * ξ (PositivityTheory.RgEis.rep r * g)) *
      PositivityTheory.RgEis.pos Δ P l₁ (PositivityTheory.RgEis.rep r * g)) →
    (∀ g, Summable fun r : PositivityTheory.RgEis.Cos Δ Γ => Real.exp (e₁ * ξ (PositivityTheory.RgEis.rep r * g)) *
      PositivityTheory.RgEis.pos Δ P' l₂ (PositivityTheory.RgEis.rep r * g)) →
    (∀ g, Summable fun r : PositivityTheory.RgEis.Cos Δ Γ => Real.exp (e₂ * ξ (PositivityTheory.RgEis.rep r * g)) *
      PositivityTheory.RgEis.pos Δ P' l₂ (PositivityTheory.RgEis.rep r * g)) →
    ∀ g : G, ∃ U ∈ 𝓝 g, ∃ u : PositivityTheory.RgEis.Cos Δ Γ → ℝ, Summable u ∧
      ∀ l : ℂ × ℂ, b ≤ l.1.re → l.1.re ≤ a → e₁ ≤ l.2.re → l.2.re ≤ e₂ → ∀ g' ∈ U, ∀ r,
        ‖Complex.exp (l.2 * ξ (PositivityTheory.RgEis.rep r * g')) • H l.1 (PositivityTheory.RgEis.rep r * g')‖ ≤ u r := by
  intro G _ _ _ _ X _ _ Γ Δ P P' ξ l₁ l₂ H a b e₁ e₂ M hξ hl₁ hl₂ hc₁ hc₂ hH s11 s21 s12 s22 g
  obtain ⟨C, hC1, -, hCc⟩ := local_compact_nhds (x := (1 : G)) Filter.univ_mem
  obtain ⟨Aξ, hAξ⟩ := hξ C hCc
  obtain ⟨A₁, hA₁⟩ := hl₁ C hCc
  obtain ⟨A₂, hA₂⟩ := hl₂ C hCc
  have hU : (fun g' => g⁻¹ * g') ⁻¹' C ∈ 𝓝 g := by
    apply (continuous_mul_left g⁻¹).continuousAt.preimage_mem_nhds
    simpa using hC1
  refine ⟨(fun g' => g⁻¹ * g') ⁻¹' C, hU, fun r => |M| *
      (Real.exp (|e₁| * Aξ) * Real.exp A₁ * (Real.exp (e₁ * ξ (rep r * g)) * pos Δ P l₁ (rep r * g)) +
        Real.exp (|e₂| * Aξ) * Real.exp A₁ * (Real.exp (e₂ * ξ (rep r * g)) * pos Δ P l₁ (rep r * g)) +
        Real.exp (|e₁| * Aξ) * Real.exp A₂ * (Real.exp (e₁ * ξ (rep r * g)) * pos Δ P' l₂ (rep r * g)) +
        Real.exp (|e₂| * Aξ) * Real.exp A₂ * (Real.exp (e₂ * ξ (rep r * g)) * pos Δ P' l₂ (rep r * g))), ?_, ?_⟩
  · exact Summable.mul_left |M|
      ((((s11 g).mul_left (Real.exp (|e₁| * Aξ) * Real.exp A₁)).add
        ((s21 g).mul_left (Real.exp (|e₂| * Aξ) * Real.exp A₁))).add
        ((s12 g).mul_left (Real.exp (|e₁| * Aξ) * Real.exp A₂)) |>.add
        ((s22 g).mul_left (Real.exp (|e₂| * Aξ) * Real.exp A₂)))
  · intro l hb ha he₁ he₂ g' hg' r
    have hw : g⁻¹ * g' ∈ C := hg'
    have hy : rep r * g' = rep r * g * (g⁻¹ * g') := by
      rw [mul_assoc, mul_inv_cancel_left]
    have hnorm : ‖Complex.exp (l.2 * ξ (rep r * g')) • H l.1 (rep r * g')‖ =
        Real.exp (l.2.re * ξ (rep r * g')) * ‖H l.1 (rep r * g')‖ := by
      rw [norm_smul, Complex.norm_exp]
      simp [Complex.mul_re]
    have hξw := hAξ (rep r * g) (g⁻¹ * g') hw
    rw [← hy] at hξw
    have hexp : Real.exp (l.2.re * ξ (rep r * g')) ≤
        Real.exp (|e₁| * Aξ) * Real.exp (e₁ * ξ (rep r * g)) +
          Real.exp (|e₂| * Aξ) * Real.exp (e₂ * ξ (rep r * g)) := by
      have h0 := exp_between e₁ e₂ l.2.re (ξ (rep r * g')) he₁ he₂
      have h1 := exp_shift e₁ (ξ (rep r * g')) (ξ (rep r * g)) Aξ hξw
      have h2 := exp_shift e₂ (ξ (rep r * g')) (ξ (rep r * g)) Aξ hξw
      linarith
    have hp1 : pos Δ P l₁ (rep r * g') ≤ Real.exp A₁ * pos Δ P l₁ (rep r * g) := by
      rw [hy]
      exact pos_mul_le Δ P l₁ C A₁ hA₁ hc₁ (rep r * g) (g⁻¹ * g') hw
    have hp2 : pos Δ P' l₂ (rep r * g') ≤ Real.exp A₂ * pos Δ P' l₂ (rep r * g) := by
      rw [hy]
      exact pos_mul_le Δ P' l₂ C A₂ hA₂ hc₂ (rep r * g) (g⁻¹ * g') hw
    have hH1 := hH l.1 hb ha (rep r * g')
    have hs0 : 0 ≤ pos Δ P l₁ (rep r * g') + pos Δ P' l₂ (rep r * g') :=
      add_nonneg (pos_nonneg' _ _ _ _) (pos_nonneg' _ _ _ _)
    have hH2 : ‖H l.1 (rep r * g')‖ ≤ |M| * (pos Δ P l₁ (rep r * g') + pos Δ P' l₂ (rep r * g')) :=
      hH1.trans (mul_le_mul_of_nonneg_right (le_abs_self M) hs0)
    have hE0 : 0 ≤ Real.exp (|e₁| * Aξ) * Real.exp (e₁ * ξ (rep r * g)) +
        Real.exp (|e₂| * Aξ) * Real.exp (e₂ * ξ (rep r * g)) := by positivity
    rw [hnorm]
    calc Real.exp (l.2.re * ξ (rep r * g')) * ‖H l.1 (rep r * g')‖
        ≤ Real.exp (l.2.re * ξ (rep r * g')) *
            (|M| * (pos Δ P l₁ (rep r * g') + pos Δ P' l₂ (rep r * g'))) :=
          mul_le_mul_of_nonneg_left hH2 (Real.exp_pos _).le
      _ ≤ (Real.exp (|e₁| * Aξ) * Real.exp (e₁ * ξ (rep r * g)) +
            Real.exp (|e₂| * Aξ) * Real.exp (e₂ * ξ (rep r * g))) *
            (|M| * (pos Δ P l₁ (rep r * g') + pos Δ P' l₂ (rep r * g'))) :=
          mul_le_mul_of_nonneg_right hexp (mul_nonneg (abs_nonneg M) hs0)
      _ ≤ (Real.exp (|e₁| * Aξ) * Real.exp (e₁ * ξ (rep r * g)) +
            Real.exp (|e₂| * Aξ) * Real.exp (e₂ * ξ (rep r * g))) *
            (|M| * (Real.exp A₁ * pos Δ P l₁ (rep r * g) + Real.exp A₂ * pos Δ P' l₂ (rep r * g))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add hp1 hp2) (abs_nonneg M)) hE0
      _ = _ := by ring

end GlobalTheory.CompanionTheory.EisCross
