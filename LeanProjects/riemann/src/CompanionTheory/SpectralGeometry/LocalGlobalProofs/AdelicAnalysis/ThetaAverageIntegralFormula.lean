import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaAverageExpectedCountStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaSeriesSummableStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Core.ThetaIntegral

theorem thTerm_zero {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ) (φ : (ι → A F) → ℂ)
    (τ : InfinitePlace F → ℂ) : thTerm B ρ P gf gi φ τ 0 = φ 0 := by
  have h1 : (fun j : ι => algebraMap F (A F) ((0 : ι → F) j)) = 0 := by
    funext j; simp
  have h2 : ∀ w, (fun j : ι => ρ w ((0 : ι → F) j)) = 0 := by
    intro w; funext j; simp
  simp only [thTerm, gauss, h1, h2, mulVec_zero]
  simp

theorem main : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) (gf : Ω → Matrix ι ι (A F)) (gi : Ω → InfinitePlace F → Matrix ι ι ℝ), CountData M B ρ Pr gf gi → ∀ φ τ, SB φ → (∀ w, 0 < (τ w).im) → Integrable (fun ω => theta B ρ P (gf ω) (gi ω) φ τ) Pr ∧ ENNReal.ofReal ‖(∫ ω, theta B ρ P (gf ω) (gi ω) φ τ ∂Pr) - φ 0‖ ≤ ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, ‖thTerm B ρ P (gf ω) (gi ω) φ τ x.1‖ₑ ∂Pr := by
  intro F _ _ _ _ lf _ _ ψ _ ι _ _ M B ρ P hQ Ω _ Pr gf gi hC φ τ hφ hτ
  haveI : IsProbabilityMeasure Pr := hC.1
  have horth : ∀ ω, IsOrth B ρ (gf ω) (gi ω) := hC.2.2.2.1
  haveI : Countable F :=
    Function.Injective.countable (Module.finBasis ℚ F).equivFun.injective
  obtain ⟨w0, -, h0⟩ := Finset.exists_min_image Finset.univ (fun w => (τ w).im) Finset.univ_nonempty
  obtain ⟨w1, -, h1⟩ := Finset.exists_max_image Finset.univ (fun w => (τ w).im) Finset.univ_nonempty
  have ht : 0 < (τ w0).im := hτ w0
  have hs : 0 < (τ w1).im := hτ w1
  obtain ⟨C, hCb⟩ := GlobalTheory.T.weighted_theta_average_le_of_countData F ι M B ρ P hQ Ω Pr gf gi hC φ hφ
    ((τ w0).im / (τ w1).im) (τ w0).im (div_pos ht hs) ht
  obtain ⟨hmeas, hbd⟩ := hCb τ (fun w => h0 w (Finset.mem_univ w)) (by
    intro v w
    have hw : (τ w).im ≤ (τ w1).im := h1 w (Finset.mem_univ w)
    have hv : (τ w0).im ≤ (τ v).im := h0 v (Finset.mem_univ v)
    calc (τ w0).im / (τ w1).im * (τ w).im ≤ (τ w0).im / (τ w1).im * (τ w1).im :=
          mul_le_mul_of_nonneg_left hw (div_pos ht hs).le
      _ = (τ w0).im := div_mul_cancel₀ _ hs.ne'
      _ ≤ (τ v).im := hv)
  have hwt : 0 < wt M τ := Finset.prod_pos fun w _ => pow_pos (Real.sqrt_pos.2 (hτ w)) M
  have hfin : (∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, ‖thTerm B ρ P (gf ω) (gi ω) φ τ x.1‖ₑ ∂Pr) ≠ ∞ := by
    intro h
    rw [h, ENNReal.mul_top (by simpa using hwt)] at hbd
    simp at hbd
  have hsum : ∀ ω, Summable (thTerm B ρ P (gf ω) (gi ω) φ τ) := fun ω =>
    ((GlobalTheory.T.theta_series_summable F ι M B ρ P hQ (gf ω) (gi ω) (horth ω) τ hτ).1 φ hφ).of_norm
  have hsub : ∀ ω, Summable fun x : {x : ι → F // x ≠ 0} => thTerm B ρ P (gf ω) (gi ω) φ τ x.1 :=
    fun ω => (hsum ω).subtype _
  set g : Ω → ℂ := fun ω => ∑' x : {x : ι → F // x ≠ 0}, thTerm B ρ P (gf ω) (gi ω) φ τ x.1 with hg
  have hsplit : ∀ ω, theta B ρ P (gf ω) (gi ω) φ τ = φ 0 + g ω := by
    intro ω
    have h := (hsum ω).tsum_subtype_add_tsum_subtype_compl ({0} : Set (ι → F))
    rw [tsum_singleton, thTerm_zero] at h
    exact h.symm
  have hgm : Measurable g :=
    measurable_of_tendsto_metrizable' Filter.atTop
      (f := fun (s : Finset {x : ι → F // x ≠ 0}) ω => ∑ x ∈ s, thTerm B ρ P (gf ω) (gi ω) φ τ x.1)
      (fun s => Finset.measurable_sum _ fun x _ => hmeas x.1)
      (tendsto_pi_nhds.2 fun ω => (hsub ω).hasSum)
  have hgI : ∫⁻ ω, ‖g ω‖ₑ ∂Pr ≤
      ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, ‖thTerm B ρ P (gf ω) (gi ω) φ τ x.1‖ₑ ∂Pr :=
    lintegral_mono fun ω => enorm_tsum_le_tsum_enorm
  have hgint : Integrable g Pr := ⟨hgm.aestronglyMeasurable, lt_of_le_of_lt hgI hfin.lt_top⟩
  have hth : (fun ω => theta B ρ P (gf ω) (gi ω) φ τ) = fun ω => φ 0 + g ω := funext hsplit
  refine ⟨by rw [hth]; exact (integrable_const _).add hgint, ?_⟩
  have hint : (∫ ω, theta B ρ P (gf ω) (gi ω) φ τ ∂Pr) - φ 0 = ∫ ω, g ω ∂Pr := by
    rw [hth, integral_add (integrable_const _) hgint]
    simp
  rw [hint, ofReal_norm_eq_enorm]
  exact (enorm_integral_le_lintegral_enorm g).trans hgI

end GlobalTheory.CompanionTheory.SW.Core.ThetaIntegral
