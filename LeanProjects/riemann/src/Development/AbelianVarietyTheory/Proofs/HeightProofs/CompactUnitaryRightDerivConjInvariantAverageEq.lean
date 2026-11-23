import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KAvgDeriv

open MeasureTheory Filter Topology GlobalTheory.KFourier

variable {n : ℕ}

theorem toMK_expK_real {ε : Fin n → Bool} {X : Mx n} (hX : inK ε X) (t : ℝ) :
    toMK (expK ε X t) = NormedSpace.exp (t • X) := by
  rw [toMK_expK hX t, Complex.coe_smul]

theorem toMK_mem_UJ {ε : Fin n → Bool} (k : KG ε) : toMK k ∈ UJset ε := K_le_UJ (toMK_mem_K k)

theorem integral_conj_swap {ε : Fin n → Bool} (e : KG ε → ℂ) (he : ∀ a k : KG ε, e (a * k * a⁻¹) = e k)
    (φ : Mx n → ℂ) (g : Mx n) (κ : KG ε) :
    ∫ k, e k * φ (g * toMK κ * toMK k) ∂(muK ε) = ∫ k, e k * φ (g * toMK k * toMK κ) ∂(muK ε) := by
  have h1 := integral_mul_left_eq_self (μ := muK ε) (fun k => e k * φ (g * toMK κ * toMK k)) κ⁻¹
  have h2 := integral_mul_right_eq_self (μ := muK ε) (fun k => e (κ⁻¹ * k) * φ (g * toMK k)) κ
  have ea : ∀ k, g * toMK κ * toMK (κ⁻¹ * k) = g * toMK k := fun k => by
    rw [mul_assoc, ← toMK_mul, mul_inv_cancel_left]
  have eb : ∀ k, e (κ⁻¹ * (k * κ)) = e k := fun k => by
    have := he κ⁻¹ k
    rwa [inv_inv, mul_assoc] at this
  calc ∫ k, e k * φ (g * toMK κ * toMK k) ∂(muK ε)
      = ∫ k, e (κ⁻¹ * k) * φ (g * toMK κ * toMK (κ⁻¹ * k)) ∂(muK ε) := h1.symm
    _ = ∫ k, e (κ⁻¹ * k) * φ (g * toMK k) ∂(muK ε) := by simp only [ea]
    _ = ∫ k, e (κ⁻¹ * (k * κ)) * φ (g * toMK (k * κ)) ∂(muK ε) := h2.symm
    _ = _ := by simp only [eb, toMK_mul, mul_assoc]

variable {ε : Fin n → Bool} {F : List (Mx n) → Mx n → ℂ}

theorem measurable_fam (hD : IsDerFam ε F) {f : Mx n → ℂ} (hf : ContinuousOn f (UJset ε))
    (hF0 : ∀ g ∈ UJset ε, F [] g = f g) :
    ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ a ∈ UJset ε, ∀ b ∈ UJset ε,
      Measurable fun k : KG ε => F l (a * toMK k * b) := by
  intro l
  induction l with
  | nil =>
    intro _ a ha b hb
    have hm : ∀ k : KG ε, a * toMK k * b ∈ UJset ε := fun k => mul_mem_UJ (mul_mem_UJ ha (toMK_mem_UJ k)) hb
    have e1 : (fun k : KG ε => F [] (a * toMK k * b)) = fun k => f (a * toMK k * b) :=
      funext fun k => hF0 _ (hm k)
    rw [e1]
    exact (hf.comp_continuous ((continuous_const.mul (continuous_toMK ε)).mul continuous_const) hm).measurable
  | cons X l ih =>
    intro hl a ha b hb
    have hX : X ∈ lieSet ε := hl X List.mem_cons_self
    have hl' : ∀ Y ∈ l, Y ∈ lieSet ε := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)
    let s : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
    have hs0 : Tendsto s atTop (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall fun m => by simp only [Set.mem_compl_iff, Set.mem_singleton_iff, s]; positivity⟩
    have hmeas : ∀ m : ℕ, Measurable fun k : KG ε =>
        (s m)⁻¹ • (F l (a * toMK k * (b * NormedSpace.exp (s m • X))) - F l (a * toMK k * b)) := fun m => by
      have := ((ih hl' a ha _ (mul_mem_UJ hb (exp_mem_UJ hX (s m)))).sub (ih hl' a ha b hb)).const_smul (s m)⁻¹
      exact this
    refine measurable_of_tendsto_metrizable hmeas (tendsto_pi_nhds.2 fun k => ?_)
    have hg : a * toMK k * b ∈ UJset ε := mul_mem_UJ (mul_mem_UJ ha (toMK_mem_UJ k)) hb
    have hd := (hasDerivAt_iff_tendsto_slope.1 (hD l hl' X hX _ hg)).comp hs0
    refine hd.congr fun m => ?_
    simp only [Function.comp_apply, slope_def_module, sub_zero, zero_smul, NormedSpace.exp_zero, mul_one,
      mul_assoc]

theorem hasDerivAt_avg (hD : IsDerFam ε F) {N : ℕ} (hG : FamGrowth ε N F) {f : Mx n → ℂ}
    (hf : ContinuousOn f (UJset ε)) (hF0 : ∀ g ∈ UJset ε, F [] g = f g) {e : KG ε → ℂ} (hec : Continuous e)
    (he : ∀ a k : KG ε, e (a * k * a⁻¹) = e k) {l : List (Mx n)} (hl : ∀ Y ∈ l, Y ∈ lieSet ε) {X : Mx n}
    (hX : inK ε X) {g : Mx n} (hg : g ∈ UJset ε) :
    HasDerivAt (fun t : ℝ => ∫ k, e k * F l (g * toMK (expK ε X t) * toMK k) ∂(muK ε))
      (∫ k, e k * F (X :: l) (g * toMK k) ∂(muK ε)) 0 := by
  have hXl : X ∈ lieSet ε := hX.1
  have hl' : ∀ Y ∈ X :: l, Y ∈ lieSet ε := by
    intro Y hY
    rcases List.mem_cons.1 hY with rfl | h
    exacts [hXl, hl Y h]
  have hre : (fun t : ℝ => ∫ k, e k * F l (g * toMK (expK ε X t) * toMK k) ∂(muK ε)) =
      fun t => ∫ k, e k * F l (g * toMK k * NormedSpace.exp (t • X)) ∂(muK ε) := by
    funext t
    rw [integral_conj_swap e he, toMK_expK_real hX]
  rw [hre]
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hec.continuousOn
  obtain ⟨C, hC⟩ := hG (X :: l) hl'
  obtain ⟨C0, hC0⟩ := hG l hl
  have hmem : ∀ (k : KG ε) (s : ℝ), g * toMK k * NormedSpace.exp (s • X) ∈ UJset ε := fun k s =>
    mul_mem_UJ (mul_mem_UJ hg (toMK_mem_UJ k)) (exp_mem_UJ hXl s)
  have hhs : ∀ (k : KG ε) (s : ℝ), hs (g * toMK k * NormedSpace.exp (s • X)) = hs g := fun k s => by
    rw [← toMK_expK_real hX, mul_assoc, ← toMK_mul]
    exact ((hermitian_small_ball n ε).2 _ _ (toMK_mem_K _)).1
  have hem : Measurable e := hec.measurable
  have hbd : ∀ (l' : List (Mx n)) (C' : ℝ), (∀ h ∈ UJset ε, ‖F l' h‖ ≤ C' * (1 + hs h) ^ N) →
      ∀ (k : KG ε) (s : ℝ), ‖e k * F l' (g * toMK k * NormedSpace.exp (s • X))‖ ≤ M * (C' * (1 + hs g) ^ N) :=
    fun l' C' hC' k s => by
      rw [norm_mul]
      refine mul_le_mul (hM k trivial) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hM k trivial))
      rw [← hhs k s]
      exact hC' _ (hmem k s)
  have hmeasF : ∀ t : ℝ, AEStronglyMeasurable (fun k => e k * F l (g * toMK k * NormedSpace.exp (t • X))) (muK ε) :=
    fun t => (hem.mul (measurable_fam hD hf hF0 l hl g hg _ (exp_mem_UJ hXl t))).aestronglyMeasurable
  have hmeasF' : AEStronglyMeasurable (fun k => e k * F (X :: l) (g * toMK k * NormedSpace.exp ((0 : ℝ) • X)))
      (muK ε) := (hem.mul (measurable_fam hD hf hF0 (X :: l) hl' g hg _ (exp_mem_UJ hXl 0))).aestronglyMeasurable
  have hint : Integrable (fun k => e k * F l (g * toMK k * NormedSpace.exp ((0 : ℝ) • X))) (muK ε) :=
    Integrable.mono' (integrable_const (M * (C0 * (1 + hs g) ^ N))) (hmeasF 0) (ae_of_all _ fun k => hbd l C0 hC0 k 0)
  have hdif : ∀ (k : KG ε) (s : ℝ), HasDerivAt (fun t : ℝ => e k * F l (g * toMK k * NormedSpace.exp (t • X)))
      (e k * F (X :: l) (g * toMK k * NormedSpace.exp (s • X))) s := fun k s => by
    have h1 := hD l hl X hXl _ (hmem k s)
    have h2 : HasDerivAt (fun t : ℝ => F l (g * toMK k * NormedSpace.exp (s • X) * NormedSpace.exp ((t - s) • X)))
        (F (X :: l) (g * toMK k * NormedSpace.exp (s • X))) s :=
      HasDerivAt.comp_sub_const (f := fun t : ℝ => F l (g * toMK k * NormedSpace.exp (s • X) * NormedSpace.exp (t • X)))
        s s (by rw [sub_self]; exact h1)
    have e2 : (fun t : ℝ => F l (g * toMK k * NormedSpace.exp (s • X) * NormedSpace.exp ((t - s) • X))) =
        fun t => F l (g * toMK k * NormedSpace.exp (t • X)) := by
      funext t
      rw [mul_assoc (g * toMK k), ← exp_add_smul, add_sub_cancel]
    rw [e2] at h2
    exact h2.const_mul (e k)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := muK ε) (x₀ := (0 : ℝ))
    (F := fun t k => e k * F l (g * toMK k * NormedSpace.exp (t • X)))
    (F' := fun t k => e k * F (X :: l) (g * toMK k * NormedSpace.exp (t • X)))
    (bound := fun _ => M * (C * (1 + hs g) ^ N)) (s := Set.univ) Filter.univ_mem (Eventually.of_forall hmeasF) hint hmeasF'
    (ae_of_all _ fun k t _ => hbd (X :: l) C hC k t) (integrable_const _) (ae_of_all _ fun k s _ => hdif k s)
  have e3 : (fun k => e k * F (X :: l) (g * toMK k * NormedSpace.exp ((0 : ℝ) • X))) =
      fun k => e k * F (X :: l) (g * toMK k) := by
    funext k
    rw [zero_smul, NormedSpace.exp_zero, mul_one]
  simpa only [e3] using key.2

theorem rder_avgK_all (hD : IsDerFam ε F) {N : ℕ} (hG : FamGrowth ε N F) {f : Mx n → ℂ}
    (hf : ContinuousOn f (UJset ε)) (hF0 : ∀ g ∈ UJset ε, F [] g = f g) {e : KG ε → ℂ} (hec : Continuous e)
    (he : ∀ a k : KG ε, e (a * k * a⁻¹) = e k) {y : Mx n} (hy : y ∈ UJset ε) :
    ∀ u : List (Mx n), (∀ X ∈ u, inK ε X) → ∀ k' : KG ε,
      rder ε u (avgK ε e f y) k' = ∫ k, e k * F u (y * toMK k' * toMK k) ∂(muK ε) := by
  intro u
  induction u with
  | nil =>
    intro _ k'
    rw [rder_nil]
    refine integral_congr_ae (ae_of_all _ fun k => ?_)
    simp only
    rw [hF0 _ (mul_mem_UJ (mul_mem_UJ hy (toMK_mem_UJ k')) (toMK_mem_UJ k))]
  | cons X l ih =>
    intro hu k'
    have hX : inK ε X := hu X List.mem_cons_self
    have hlK : ∀ Y ∈ l, inK ε Y := fun Y hY => hu Y (List.mem_cons_of_mem _ hY)
    have hl : ∀ Y ∈ l, Y ∈ lieSet ε := fun Y hY => (hlK Y hY).1
    rw [rder_cons]
    have e1 : (fun t : ℝ => rder ε l (avgK ε e f y) (k' * expK ε X t)) =
        fun t => ∫ k, e k * F l (y * toMK k' * toMK (expK ε X t) * toMK k) ∂(muK ε) := by
      funext t
      rw [ih hlK, toMK_mul, mul_assoc y]
    rw [e1]
    exact (hasDerivAt_avg hD hG hf hF0 hec he hl hX (mul_mem_UJ hy (toMK_mem_UJ k'))).deriv

theorem rder_avgK_one (ε : Fin n → Bool) (N : ℕ) (F : List (Mx n) → Mx n → ℂ) (hD : IsDerFam ε F)
    (hG : FamGrowth ε N F) (f : Mx n → ℂ) (hf : ContinuousOn f (UJset ε)) (hF0 : ∀ g ∈ UJset ε, F [] g = f g)
    (e : KG ε → ℂ) (hec : Continuous e) (he : ∀ a k : KG ε, e (a * k * a⁻¹) = e k) (u : List (Mx n))
    (hu : ∀ X ∈ u, inK ε X) (y : Mx n) (hy : y ∈ UJset ε) :
    GlobalTheory.KFourier.rder ε u (GlobalTheory.KFourier.avgK ε e f y) 1 = ∫ k, e k * F u (y * toMK k) ∂(muK ε) := by
  rw [rder_avgK_all hD hG hf hF0 hec he hy u hu 1, toMK_one, mul_one]

end GlobalTheory.KAvgDeriv
