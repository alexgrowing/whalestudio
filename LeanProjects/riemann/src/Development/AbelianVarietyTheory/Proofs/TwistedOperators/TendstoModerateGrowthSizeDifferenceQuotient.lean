import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RWordRTrAdelic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsModGrowthExpLeNormInfPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspFunctionClosedUnderOperations
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GrowthSizeRWordNeTopOfLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grow GlobalTheory.Size GlobalTheory.Mem.AutSpace Filter
open scoped ENNReal NNReal Topology

namespace GlobalTheory.Size.DiffQuot

theorem norm_taylor_le {f f₁ f₂ : ℝ → ℂ} (d1 : ∀ s, HasDerivAt f (f₁ s) s) (d2 : ∀ s, HasDerivAt f₁ (f₂ s) s)
    {B t : ℝ} (hB0 : 0 ≤ B) (hB : ∀ s ∈ Set.Icc (-|t|) |t|, ‖f₂ s‖ ≤ B) :
    ‖f t - f 0 - (t : ℂ) * f₁ 0‖ ≤ B * |t| * |t| := by
  have hI : Convex ℝ (Set.Icc (-|t|) |t|) := convex_Icc _ _
  have h0 : (0 : ℝ) ∈ Set.Icc (-|t|) |t| := ⟨neg_nonpos.mpr (abs_nonneg t), abs_nonneg t⟩
  have ht : t ∈ Set.Icc (-|t|) |t| := ⟨neg_abs_le t, le_abs_self t⟩

  have h1 : ∀ s ∈ Set.Icc (-|t|) |t|, ‖f₁ s - f₁ 0‖ ≤ B * |t| := by
    intro s hs
    have hmv := hI.norm_image_sub_le_of_norm_hasDerivWithin_le (f := f₁) (f' := f₂)
      (fun x _ => (d2 x).hasDerivWithinAt) hB h0 hs
    refine hmv.trans ?_
    rw [sub_zero, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨hs.1, hs.2⟩) hB0

  have hg : ∀ s ∈ Set.Icc (-|t|) |t|, HasDerivWithinAt (fun u : ℝ => f u - (u : ℂ) * f₁ 0) (f₁ s - f₁ 0)
      (Set.Icc (-|t|) |t|) s := by
    intro s _
    have hc : HasDerivAt (fun u : ℝ => (u : ℂ) * f₁ 0) (f₁ 0) s := by
      simpa using ((hasDerivAt_id s).ofReal_comp).mul_const (f₁ 0)
    exact ((d1 s).sub hc).hasDerivWithinAt
  have hmv := hI.norm_image_sub_le_of_norm_hasDerivWithin_le hg h1 h0 ht
  have e : f t - f 0 - (t : ℂ) * f₁ 0 = (f t - (t : ℂ) * f₁ 0) - (f 0 - ((0 : ℝ) : ℂ) * f₁ 0) := by
    push_cast; ring
  rw [e]
  refine hmv.trans (le_of_eq ?_)
  rw [sub_zero, Real.norm_eq_abs]

theorem tendsto_growthSize_diffQuot : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (N : ℕ), ∀ X ∈ lieAt V τ, ∀ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V, GlobalTheory.Size.growthSob θ V 2 N φ ≠ ⊤ → Filter.Tendsto (fun t : ℝ => GlobalTheory.Size.growthSize V N (((t : ℂ)⁻¹) • (rTr V (oneP θ V τ X t) φ - φ) - Rder θ V τ X φ)) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
  intro D θ hθ V τ N X hX φ hφ hS
  have hφ1 : Rder θ V τ X φ ∈ SmFun θ V := Rder_mem hφ hX

  have hw : growthSize V N (Rder θ V τ X (Rder θ V τ X φ)) ≠ ⊤ := by
    have hl : IsLieWord V [(τ, X), (τ, X)] := by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> exact hX
    have h2 := growthSize_rWord_ne_top_of_le hθ hφ hS hl (by simp)
    simpa only [rWord, wordAct_cons, wordAct_nil] using h2
  obtain ⟨C, hC⟩ := modGrowthExp_iff.2 hw
  have hC0 : 0 ≤ C := nonneg_of_growth hC

  obtain ⟨K, hK⟩ := exists_height_le_of_isCompact V
    (isCompact_Icc.image (GlobalTheory.Mem.Lift.continuous_oneP hθ hX) :
      IsCompact (oneP θ V τ X '' Set.Icc (-1 : ℝ) 1))
  have hK1 : 1 ≤ K := (one_le_height V _).trans (hK _ ⟨0, ⟨by norm_num, by norm_num⟩, rfl⟩)
  have hK0 : 0 ≤ K := by linarith

  have key : ∀ t : ℝ, |t| ≤ 1 → t ≠ 0 → ∀ g,
      ‖(((t : ℂ)⁻¹) • (rTr V (oneP θ V τ X t) φ - φ) - Rder θ V τ X φ) g‖ ≤
        C * K ^ N * |t| * height V g ^ N := by
    intro t ht1 ht0 g
    have d1 : ∀ s, HasDerivAt (fun s => φ (g * oneP θ V τ X s)) (Rder θ V τ X φ (g * oneP θ V τ X s)) s :=
      fun s => GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (fun g' => GlobalTheory.Mem.Lift.hasDerivAt_Rder hφ hX g') g s
    have d2 : ∀ s, HasDerivAt (fun s => Rder θ V τ X φ (g * oneP θ V τ X s))
        (Rder θ V τ X (Rder θ V τ X φ) (g * oneP θ V τ X s)) s :=
      fun s => GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (fun g' => GlobalTheory.Mem.Lift.hasDerivAt_Rder hφ1 hX g') g s
    have hg0 : 0 ≤ height V g := (height_pos V g).le
    have hB0 : 0 ≤ C * (height V g * K) ^ N := mul_nonneg hC0 (pow_nonneg (mul_nonneg hg0 hK0) N)
    have hB : ∀ s ∈ Set.Icc (-|t|) |t|,
        ‖Rder θ V τ X (Rder θ V τ X φ) (g * oneP θ V τ X s)‖ ≤ C * (height V g * K) ^ N := by
      intro s hs
      have hs1 : s ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
      refine (hC _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos V _).le ?_ N) hC0)
      exact (height_mul_le V _ _).trans (mul_le_mul_of_nonneg_left (hK _ ⟨s, hs1, rfl⟩) hg0)
    have hT := norm_taylor_le d1 d2 hB0 hB
    have e0 : oneP θ V τ X 0 = 1 := GlobalTheory.Mem.Lift.oneP_zero (V := V) (τ := τ) (X := X) hθ
    have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
    have hval : (((t : ℂ)⁻¹) • (rTr V (oneP θ V τ X t) φ - φ) - Rder θ V τ X φ) g =
        (t : ℂ)⁻¹ * (φ (g * oneP θ V τ X t) - φ (g * oneP θ V τ X 0) -
          (t : ℂ) * Rder θ V τ X φ (g * oneP θ V τ X 0)) := by
      simp only [e0, mul_one, rTr, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
    have hta : 0 < |t| := abs_pos.mpr ht0
    rw [hval, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
    calc |t|⁻¹ * ‖φ (g * oneP θ V τ X t) - φ (g * oneP θ V τ X 0) -
          (t : ℂ) * Rder θ V τ X φ (g * oneP θ V τ X 0)‖
        ≤ |t|⁻¹ * (C * (height V g * K) ^ N * |t| * |t|) :=
          mul_le_mul_of_nonneg_left hT (inv_nonneg.mpr hta.le)
      _ = C * K ^ N * |t| * height V g ^ N := by
          field_simp
          ring

  have hev : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) {0}ᶜ, |t| ≤ 1 ∧ t ∈ ({0}ᶜ : Set ℝ) := by
    refine (eventually_nhdsWithin_of_eventually_nhds ?_).and eventually_mem_nhdsWithin
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with t ht
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
    exact ht.le
  have hle : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) {0}ᶜ,
      GlobalTheory.Size.growthSize V N (((t : ℂ)⁻¹) • (rTr V (oneP θ V τ X t) φ - φ) - Rder θ V τ X φ) ≤
        ENNReal.ofReal (C * K ^ N * |t|) := by
    filter_upwards [hev] with t ht
    have ht0 : t ≠ 0 := by simpa using ht.2
    exact (growthSize_le_iff (mul_nonneg (mul_nonneg hC0 (pow_nonneg hK0 N)) (abs_nonneg t))).2
      (key t ht.1 ht0)
  have hlim : Filter.Tendsto (fun t : ℝ => ENNReal.ofReal (C * K ^ N * |t|)) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    have h0 : Filter.Tendsto (fun t : ℝ => C * K ^ N * |t|) (nhds 0) (nhds 0) := by
      simpa using (continuous_abs.tendsto (0 : ℝ)).const_mul (C * K ^ N)
    simpa using (ENNReal.tendsto_ofReal h0).mono_left nhdsWithin_le_nhds
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Filter.Eventually.of_forall fun _ => zero_le) hle

end GlobalTheory.Size.DiffQuot

end
