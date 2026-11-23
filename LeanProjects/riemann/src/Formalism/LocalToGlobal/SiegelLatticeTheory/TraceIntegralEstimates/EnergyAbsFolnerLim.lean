import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyAbs
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsBasic
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsFolnerExp

noncomputable section

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem Fk_enorm_le {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {S : Set G}
    {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    (z z' : G) {q : G} (hq : q ∈ S) :
    ‖Fk σ w W z z' q‖ₑ ≤ ‖⟪σ z w, σ q (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W z'‖ₑ := by
  unfold Fk
  rw [hWeq q hq z', hσ.2.1 q z', ContinuousLinearMap.mul_apply]
  have hn : ‖τ q (W z')‖ = ‖W z'‖ := by
    have h := hτu q hq (W z') (W z')
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    have h' : ‖τ q (W z')‖ ^ 2 = ‖W z'‖ ^ 2 := by exact_mod_cast h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h'
  have hA : ‖⟪τ q (W z'), W z⟫_ℂ‖ ≤ ‖W z‖ * ‖W z'‖ :=
    (norm_inner_le_norm _ _).trans (by rw [hn, mul_comm])
  have hAe : ‖⟪τ q (W z'), W z⟫_ℂ‖ₑ ≤ ‖W z‖ₑ * ‖W z'‖ₑ := by
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
      ← ENNReal.ofReal_mul (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hA
  rw [enorm_mul]
  calc ‖⟪τ q (W z'), W z⟫_ℂ‖ₑ * ‖⟪σ z w, σ q (σ z' w)⟫_ℂ‖ₑ
      ≤ (‖W z‖ₑ * ‖W z'‖ₑ) * ‖⟪σ z w, σ q (σ z' w)⟫_ℂ‖ₑ := by gcongr
    _ = ‖⟪σ z w, σ q (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W z'‖ₑ := by ring

private theorem continuous_Fk_uncurry {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {W : G → V}
    (hWc : Continuous W) : Continuous (fun x : G × G × G => Fk σ w W x.1 x.2.1 x.2.2) := by
  have hσc := hσ.2.2.2 w
  unfold Fk
  refine Continuous.mul ?_ ?_
  · exact (hWc.comp (continuous_snd.snd.mul continuous_snd.fst)).inner (hWc.comp continuous_fst)
  · exact (hσc.comp continuous_fst).inner (hσc.comp (continuous_snd.snd.mul continuous_snd.fst))

private theorem lintegral_enorm_Fk_lt_infty {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {S : Set G}
    {μS ν : Measure G} [SFinite μS] [SFinite ν] (hS0 : μS Sᶜ = 0) {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    (hmeas : Measurable (fun x : G × G × G => ‖Fk σ w W x.1 x.2.1 x.2.2‖ₑ))
    (hconv : ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪σ z w, σ s (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W z'‖ₑ ∂μS ∂ν ∂ν < ⊤) :
    ∫⁻ x, ‖Fk σ w W x.1 x.2.1 x.2.2‖ₑ ∂(ν.prod (ν.prod μS)) < ⊤ := by
  have hSae : ∀ᵐ q ∂μS, q ∈ S := by
    have h := compl_mem_ae_iff.2 hS0
    rw [compl_compl] at h
    exact h
  calc ∫⁻ x, ‖Fk σ w W x.1 x.2.1 x.2.2‖ₑ ∂(ν.prod (ν.prod μS))
      = ∫⁻ z, ∫⁻ y, ‖Fk σ w W z y.1 y.2‖ₑ ∂(ν.prod μS) ∂ν := lintegral_prod _ hmeas.aemeasurable
    _ = ∫⁻ z, ∫⁻ z', ∫⁻ q, ‖Fk σ w W z z' q‖ₑ ∂μS ∂ν ∂ν :=
        lintegral_congr fun z => lintegral_prod _ (hmeas.comp measurable_prodMk_left).aemeasurable
    _ ≤ ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪σ z w, σ s (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W z'‖ₑ ∂μS ∂ν ∂ν :=
        lintegral_mono fun z => lintegral_mono fun z' => lintegral_mono_ae (by
          filter_upwards [hSae] with q hq
          exact Fk_enorm_le hσ w hWeq hτu z z' hq)
    _ < ⊤ := hconv

theorem Fk_integrable {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {S : Set G}
    {μS ν : Measure G} [SFinite μS] [SFinite ν] (hS0 : μS Sᶜ = 0) {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    (hWc : Continuous W)
    (hconv : ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪σ z w, σ s (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W z'‖ₑ ∂μS ∂ν ∂ν < ⊤) :
    Integrable (fun x : G × G × G => Fk σ w W x.1 x.2.1 x.2.2) (ν.prod (ν.prod μS)) := by
  have hcont := continuous_Fk_uncurry hσ w hWc
  exact ⟨hcont.aestronglyMeasurable,
    lintegral_enorm_Fk_lt_infty hσ w hS0 hWeq hτu (continuous_enorm.measurable.comp hcont.measurable) hconv⟩

theorem integral_norm_sq_eq_one {ν : Measure G} {W : G → V} (hWc : Continuous W) (h2 : ∫⁻ x, ‖W x‖ₑ ^ 2 ∂ν = 1) :
    ∫ z, ‖W z‖ ^ 2 ∂ν = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => sq_nonneg _)
    ((hWc.norm.pow 2).aestronglyMeasurable)]
  have h : (fun x => ENNReal.ofReal (‖W x‖ ^ 2)) = fun x => ‖W x‖ₑ ^ 2 := by
    funext x
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  rw [h, h2]
  simp

theorem integral_inner_mul_inner_eq_norm_sq_div {μ : Measure G} [μ.IsMulLeftInvariant] {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {d : ℝ}
    (hd : 0 < d) {w : HH} {S : Set G} {τ : G → (V →L[ℂ] V)} {ν : Measure G} {W : G → V}
    (hW : IsWAbs μ σ d w S τ ν W) (z : G) :
    ∫ x, ⟪W x, W z⟫_ℂ * ⟪σ z w, σ x w⟫_ℂ ∂μ = ((‖W z‖ ^ 2 / d : ℝ) : ℂ) := by
  obtain ⟨hint, heq⟩ := hW.2.2.2.2.2.1 z
  rw [← integral_mul_left_eq_self _ z]
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hpt : ∀ y, ⟪W (z * y), W z⟫_ℂ * ⟪σ z w, σ (z * y) w⟫_ℂ =
      conj (((1 / d : ℝ) : ℂ) * ⟪W z, ((d : ℂ) * conj ⟪w, σ y w⟫_ℂ) • W (z * y)⟫_ℂ) := by
    intro y
    rw [hσ.2.1 z y, ContinuousLinearMap.mul_apply, hσ.2.2.1, inner_smul_right]
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal, inner_conj_symm]
    push_cast
    first | (field_simp; ring) | field_simp | ring
  simp_rw [hpt]
  have hself : ⟪W z, W z⟫_ℂ = ((‖W z‖ ^ 2 : ℝ) : ℂ) := by
    refine Complex.ext ?_ ?_
    · first
        | simp [inner_self_eq_norm_sq]
        | (rw [Complex.ofReal_re]; exact inner_self_eq_norm_sq (𝕜 := ℂ) (W z))
    · first
        | simp
        | (rw [Complex.ofReal_im]; exact inner_self_im (𝕜 := ℂ) (W z))
  rw [integral_conj, integral_const_mul, integral_inner hint, heq, hself, ← Complex.ofReal_mul,
    Complex.conj_ofReal]
  congr 1
  ring

theorem Fk_value {μ : Measure G} [μ.IsMulLeftInvariant] {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {d : ℝ}
    (hd : 0 < d) {w : HH} {S : Set G} {μS ν : Measure G} [SFinite μS] [SFinite ν] (hq : IsQuot μ μS ν)
    {τ : G → (V →L[ℂ] V)} {W : G → V} (hW : IsWAbs μ σ d w S τ ν W)
    (hΦ : Integrable (fun x : G × G × G => Fk σ w W x.1 x.2.1 x.2.2) (ν.prod (ν.prod μS))) :
    ∫ x, Fk σ w W x.1 x.2.1 x.2.2 ∂(ν.prod (ν.prod μS)) = ((1 / d : ℝ) : ℂ) := by
  have hWc : Continuous W := hW.2.2.2.2.1
  have hL2 := hW.2.2.2.2.2.2.2
  have hm : Measurable (fun p : G × G => p.2 * p.1) := measurable_snd.mul measurable_fst
  have hmap : μ = Measure.map (fun p : G × G => p.2 * p.1) (ν.prod μS) := by
    ext s hs
    rw [Measure.map_apply hm hs, ← lintegral_indicator_one hs, hq _ (measurable_one.indicator hs),
      ← lintegral_indicator_one (hm hs),
      lintegral_prod _ ((measurable_one.indicator (hm hs)).aemeasurable)]
    first
      | rfl
      | (simp only [Set.indicator_apply, Set.mem_preimage]; rfl)
  have hinner : ∀ z, ∫ y, Fk σ w W z y.1 y.2 ∂(ν.prod μS) = ((‖W z‖ ^ 2 / d : ℝ) : ℂ) := by
    intro z
    have hg := integral_inner_mul_inner_eq_norm_sq_div hσ hd hW z
    have hgc : Continuous (fun x : G => ⟪W x, W z⟫_ℂ * ⟪σ z w, σ x w⟫_ℂ) :=
      (hWc.inner continuous_const).mul (continuous_const.inner (hσ.2.2.2 w))
    rw [hmap, integral_map hm.aemeasurable hgc.aestronglyMeasurable] at hg
    exact hg
  rw [integral_prod _ hΦ]
  refine (integral_congr_ae (ae_of_all _ fun z => hinner z)).trans ?_
  first
    | rw [integral_complex_ofReal, integral_div, integral_norm_sq_eq_one hWc hL2]
    | rw [integral_ofReal, integral_div, integral_norm_sq_eq_one hWc hL2]

end Formalism.L2.S.Pv.EnergyAbs
