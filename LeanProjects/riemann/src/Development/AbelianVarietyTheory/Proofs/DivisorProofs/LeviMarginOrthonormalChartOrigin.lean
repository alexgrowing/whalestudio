import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfM
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DifferentiableChart
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorAndDensityNearOneInFlagChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramChartSubFormEntryLe
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.LeviOriginMargin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem chain_drop (r p : ℕ) (f : ℕ → ℝ) (g : ℝ)
    (hg : ∀ i, i + 1 < r → i + 1 ≠ p → g ≤ f i - f (i + 1)) :
    ∀ n i, i + n < r → (∀ k, i < k → k ≤ i + n → k ≠ p) → (n : ℝ) * g ≤ f i - f (i + n) := by
  intro n
  induction n with
  | zero => intro i _ _; simp
  | succ n ih =>
    intro i hr hk
    have h1 := ih i (by omega) (fun k h1 h2 => hk k h1 (by omega))
    have h2 := hg (i + n) (by omega) (hk _ (by omega) (by omega))
    have e : i + (n + 1) = i + n + 1 := by omega
    rw [e]
    push_cast
    linarith

theorem coeff_la {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (g : ℝ) (hp0 : 0 < X.p0) (hpr : X.p0 < r)
    (hg0 : 0 ≤ g)
    (h1 : ∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ X.p0 → g ≤ (la τ a : ℝ) - la τ b)
    (h2 : ∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 → g ≤ (la τ b : ℝ) - la τ a)
    (τ : X.Ψ) (a b : Fin r) (hab : b < a) :
    g ≤ sgn X.p0 a * sgn X.p0 b * ((la τ b : ℝ) - la τ a) := by
  set f : ℕ → ℝ := fun k => if h : k < r then (la τ ⟨k, h⟩ : ℝ) else 0 with hf
  have hfa : ∀ c : Fin r, f c = la τ c := fun c => by simp [hf, c.isLt]
  have hg : ∀ i, i + 1 < r → i + 1 ≠ X.p0 → g ≤ f i - f (i + 1) := by
    intro i hi hip
    have := h1 τ ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl hip
    simpa [hf, hi, show i < r by omega] using this
  have hch := chain_drop r X.p0 f g hg
  have hab' : (b : ℕ) < a := hab
  have hsame : (∀ k, (b : ℕ) < k → k ≤ b + ((a : ℕ) - b) → k ≠ X.p0) → g ≤ (la τ b : ℝ) - la τ a := by
    intro hk
    have := hch ((a : ℕ) - b) b (by omega) hk
    have e : (b : ℕ) + ((a : ℕ) - b) = a := by omega
    rw [e, hfa, hfa] at this
    have hn : (1 : ℝ) ≤ (((a : ℕ) - b : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ (a : ℕ) - b by omega)
    nlinarith
  rcases GlobalTheory.CurvMargin.coeff_cases X.p0 hab' (la τ a : ℝ) (la τ b : ℝ) with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, h', e⟩
  · rw [e]; exact hsame (fun k _ hk => by omega)
  · rw [e]; exact hsame (fun k hk _ => by omega)
  · rw [e]

    have hA := hch ((r - 1) - a) a (by omega) (fun k hk _ => by omega)
    have hB := hch (b : ℕ) 0 (by omega) (fun k _ hk => by omega)
    have eA : (a : ℕ) + ((r - 1) - a) = r - 1 := by omega
    rw [eA, hfa] at hA
    rw [zero_add] at hB
    have hB' := hB
    rw [hfa] at hB'
    have h0 := h2 τ ⟨0, by omega⟩ ⟨r - 1, by omega⟩ rfl rfl
    have f0 : f 0 = (la τ ⟨0, by omega⟩ : ℝ) := by simp [hf, show 0 < r by omega]
    have fr : f (r - 1) = (la τ ⟨r - 1, by omega⟩ : ℝ) := by simp [hf, show r - 1 < r by omega]
    have hn1 : (0 : ℝ) ≤ (((r - 1 - a : ℕ)) : ℝ) * g := by positivity
    have hn2 : (0 : ℝ) ≤ ((b : ℕ) : ℝ) * g := by positivity
    rw [fr] at hA
    rw [f0] at hB'
    linarith

theorem coeff_blk {r : ℕ} (X : Data E r) (τ : X.Ψ) (a b : Fin r) (hab : b < a) :
    0 ≤ sgn X.p0 a * sgn X.p0 b * ((GlobalTheory.CurvMargin.blockWt X τ b : ℝ) - GlobalTheory.CurvMargin.blockWt X τ a) ∧
    sgn X.p0 a * sgn X.p0 b * ((GlobalTheory.CurvMargin.blockWt X τ b : ℝ) - GlobalTheory.CurvMargin.blockWt X τ a) ≤ 1 := by
  have hab' : (b : ℕ) < a := hab
  unfold GlobalTheory.CurvMargin.blockWt sgn
  by_cases ha : (a : ℕ) < X.p0
  · have hb : (b : ℕ) < X.p0 := hab'.trans ha
    simp [ha, hb]
  · by_cases hb : (b : ℕ) < X.p0
    · simp [ha, hb]
    · simp [ha, hb]

theorem coeff_kap {r : ℕ} (X : Data E r) (τ : X.Ψ) (a b : Fin r) (hab : b < a) :
    sgn X.p0 a * sgn X.p0 b * ((kapW X τ b : ℝ) - kapW X τ a) ≤ 2 * r := by
  have hab' : (b : ℕ) < a := hab
  have ha : (a : ℕ) < r := a.isLt
  have hk : ((kapW X τ b : ℝ) - kapW X τ a) = 2 * (b : ℝ) - 2 * (a : ℝ) := by
    simp [kapW]
  rw [hk]
  have hb0 : (0 : ℝ) ≤ (b : ℝ) := by positivity
  have hba : (b : ℝ) < a := by exact_mod_cast hab'
  have har : (a : ℝ) < r := by exact_mod_cast ha
  unfold sgn
  split_ifs <;> nlinarith

theorem levi_margin_origin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r) (g bb : ℝ), 0 < X.p0 → X.p0 < r → IsOrth X x → 0 ≤ g → 0 ≤ bb → (∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ X.p0 → g ≤ (la τ a : ℝ) - la τ b) → (∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 → g ≤ (la τ b : ℝ) - la τ a) → ∀ ξ : Fin (nd X) → ℂ, (g - bb - 2 * r) * ∑ j, ‖ξ j‖ ^ 2 ≤ leviM X (phla X la) x 0 ξ - bb * leviM X (phla X (GlobalTheory.CurvMargin.blockWt X)) x 0 ξ - leviM X (phla X (kapW X)) x 0 ξ := by
  intro E _ _ _ r X la x g bb hp0 hpr ho hg0 hbb h1 h2 ξ
  have hs : ∑ j, ‖ξ j‖ ^ 2 = ∑ e : Ent X, ‖ξ (Fintype.equivFin (Ent X) e)‖ ^ 2 :=
    ((Fintype.equivFin (Ent X)).sum_comp (fun j => ‖ξ j‖ ^ 2)).symm
  rw [GlobalTheory.LeviZero.levi_phla_zero r X la x ho ξ, GlobalTheory.LeviZero.levi_phla_zero r X _ x ho ξ,
    GlobalTheory.LeviZero.levi_phla_zero r X _ x ho ξ,
    hs, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun e _ => ?_
  obtain ⟨τ, ⟨a, b⟩, hab⟩ := e
  have c1 := coeff_la X la g hp0 hpr hg0 h1 h2 τ a b hab
  have c2 := coeff_blk X τ a b hab
  have c3 := coeff_kap X τ a b hab
  set N := ‖ξ (Fintype.equivFin (Ent X) ⟨τ, ⟨(a, b), hab⟩⟩)‖ ^ 2
  have hN : 0 ≤ N := by positivity
  simp only at c1 c2 c3 ⊢
  nlinarith [mul_nonneg hbb hN, mul_nonneg (mul_nonneg hbb c2.1) hN, mul_nonneg (sub_nonneg.2 c2.2) (mul_nonneg hbb hN),
    mul_nonneg (sub_nonneg.2 c1) hN, mul_nonneg (sub_nonneg.2 c3) hN]

end GlobalTheory.LeviOriginMargin
