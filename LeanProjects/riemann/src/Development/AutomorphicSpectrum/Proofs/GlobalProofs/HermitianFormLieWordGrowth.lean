import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.NelsonExistsWordGrowthConstantStatement
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.HCForm

theorem skew_of_diag {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : Module.End ℂ E) (A : ℝ) (hA : 0 ≤ A)
    (h : ∀ x, |(⟪T x, x⟫_ℂ + ⟪x, T x⟫_ℂ).re| ≤ A * ‖x‖ ^ 2) (u v : E) :
    |(⟪T u, v⟫_ℂ + ⟪u, T v⟫_ℂ).re| ≤ A * ‖u‖ * ‖v‖ := by
  set R : E → E → ℝ := fun u v => (⟪T u, v⟫_ℂ + ⟪u, T v⟫_ℂ).re with hR
  have hsym : ∀ u v, R v u = R u v := by
    intro u v
    simp only [hR, Complex.add_re]
    rw [← inner_conj_symm (T v) u, ← inner_conj_symm v (T u)]
    simp only [Complex.conj_re]
    ring
  have hpol : ∀ u v, 4 * R u v = R (u + v) (u + v) - R (u - v) (u - v) := by
    intro u v
    have := hsym u v
    simp only [hR, map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left,
      inner_sub_right, Complex.add_re, Complex.sub_re] at this ⊢
    linarith
  have hhalf : ∀ u v, |R u v| ≤ A * (‖u‖ ^ 2 + ‖v‖ ^ 2) / 2 := by
    intro u v
    have h1 := abs_le.mp (h (u + v))
    have h2 := abs_le.mp (h (u - v))
    have hp := parallelogram_law_with_norm ℂ u v
    have e := hpol u v
    have hp' : ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2 = 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by nlinarith
    have hb : A * ‖u + v‖ ^ 2 + A * ‖u - v‖ ^ 2 = 2 * A * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
      rw [← mul_add, hp']; ring
    change |R u v| ≤ _
    have g1 : R (u + v) (u + v) ≤ A * ‖u + v‖ ^ 2 := h1.2
    have g2 : -(A * ‖u + v‖ ^ 2) ≤ R (u + v) (u + v) := h1.1
    have g3 : R (u - v) (u - v) ≤ A * ‖u - v‖ ^ 2 := h2.2
    have g4 : -(A * ‖u - v‖ ^ 2) ≤ R (u - v) (u - v) := h2.1
    rw [abs_le]
    constructor <;> nlinarith
  change |R u v| ≤ _
  rcases eq_or_ne u 0 with rfl | hu
  · simp [hR]
  rcases eq_or_ne v 0 with rfl | hv
  · simp [hR]
  have hs : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have ht : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hscale : R (((‖v‖ : ℝ) : ℂ) • u) (((‖u‖ : ℝ) : ℂ) • v) = ‖v‖ * ‖u‖ * R u v := by
    simp only [hR, map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
      Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  have hb := hhalf (((‖v‖ : ℝ) : ℂ) • u) (((‖u‖ : ℝ) : ℂ) • v)
  rw [hscale, norm_smul, norm_smul, abs_mul, abs_of_pos (mul_pos ht hs)] at hb
  simp only [Complex.norm_real, norm_norm] at hb
  have hst : 0 < ‖v‖ * ‖u‖ := mul_pos ht hs
  have : ‖v‖ * ‖u‖ * |R u v| ≤ ‖v‖ * ‖u‖ * (A * ‖u‖ * ‖v‖) := by
    calc _ ≤ _ := hb
      _ = _ := by ring
  exact le_of_mul_le_mul_left this hst

theorem nelson_inner {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {d : ℕ}
    (X : Fin d → Module.End ℂ E) (c : Fin d → Fin d → Fin d → ℂ)
    (hc : ∀ i j, X i * X j - X j * X i = ∑ l, c i j l • X l) (A : ℝ) (hA : 0 ≤ A)
    (hs : ∀ i x, |2 * (⟪X i x, x⟫_ℂ).re| ≤ A * (⟪x, x⟫_ℂ).re)
    (V : Submodule ℂ E) [FiniteDimensional ℂ V] (hV : ∀ u ∈ V, (∑ i, X i * X i) u ∈ V) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l : List (Fin d)), ∀ u ∈ V,
      Real.sqrt (⟪(l.map X).prod u, (l.map X).prod u⟫_ℂ).re ≤
        C ^ (l.length + 1) * l.length.factorial * Real.sqrt (⟪u, u⟫_ℂ).re := by
  have hsq : ∀ x : E, Real.sqrt (⟪x, x⟫_ℂ).re = ‖x‖ := by
    intro x
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
    exact Real.sqrt_sq (norm_nonneg x)
  have hskew : ∀ i u v, |(⟪X i u, v⟫_ℂ + ⟪u, X i v⟫_ℂ).re| ≤ A * ‖u‖ * ‖v‖ := by
    intro i
    refine skew_of_diag (X i) A hA ?_
    intro x
    have e : (⟪X i x, x⟫_ℂ + ⟪x, X i x⟫_ℂ).re = 2 * (⟪X i x, x⟫_ℂ).re := by
      rw [Complex.add_re, ← inner_conj_symm x (X i x), Complex.conj_re]
      ring
    have n : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    rw [e, ← n]
    exact hs i x
  obtain ⟨C, hC, hb⟩ := GlobalTheory.T.nelson_exists_word_growth_constant X c hc A hA hskew V hV
  refine ⟨C, hC, fun l u hu => ?_⟩
  rw [hsq, hsq]
  exact hb l u hu

theorem nelson_form : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (Q : M → M → ℂ)
    (hadd : ∀ x y z, Q x (y + z) = Q x y + Q x z)
    (hsmul : ∀ (c : ℂ) x y, Q x (c • y) = c * Q x y)
    (hconj : ∀ x y, Q y x = star (Q x y))
    (hpos : ∀ x, x ≠ 0 → 0 < (Q x x).re) {d : ℕ} (X : Fin d → Module.End ℂ M)
    (c : Fin d → Fin d → Fin d → ℂ) (hc : ∀ i j, X i * X j - X j * X i = ∑ l, c i j l • X l)
    (A : ℝ) (hA : 0 ≤ A) (hs : ∀ i x, |2 * (Q (X i x) x).re| ≤ A * (Q x x).re)
    (V : Submodule ℂ M) [FiniteDimensional ℂ V] (hV : ∀ u ∈ V, (∑ i, X i * X i) u ∈ V),
    ∃ C : ℝ, 0 < C ∧ ∀ (l : List (Fin d)), ∀ u ∈ V,
      Real.sqrt (Q ((l.map X).prod u) ((l.map X).prod u)).re ≤
        C ^ (l.length + 1) * l.length.factorial * Real.sqrt (Q u u).re := by
  intro M _ _ Q hadd hsmul hconj hpos d X c hc A hA hs V _ hV
  have hzero : ∀ x, Q x 0 = 0 := by
    intro x
    have := hsmul 0 x 0
    simpa using this
  have hzero' : Q 0 0 = 0 := hzero 0
  let core : InnerProductSpace.Core ℂ M :=
    { inner := Q
      conj_inner_symm := fun x y => by
        change star (Q y x) = Q x y
        rw [hconj x y, star_star]
      re_inner_nonneg := fun x => by
        change 0 ≤ (Q x x).re
        rcases eq_or_ne x 0 with rfl | hx
        · simp [hzero']
        · exact (hpos x hx).le
      add_left := fun x y z => by
        change Q (x + y) z = Q x z + Q y z
        rw [hconj z (x + y), hadd, star_add, ← hconj, ← hconj]
      smul_left := fun x y r => by
        change Q (r • x) y = star r * Q x y
        rw [hconj y (r • x), hsmul, star_mul', ← hconj]
      definite := fun x hx => by
        by_contra hne
        have h0 : Q x x = 0 := hx
        have := hpos x hne
        simp [h0] at this }
  letI : NormedAddCommGroup M := core.toNormedAddCommGroup
  letI : InnerProductSpace ℂ M := InnerProductSpace.ofCore core.toCore
  exact nelson_inner X c hc A hA hs V hV

end GlobalTheory.CompanionTheory.HCForm
