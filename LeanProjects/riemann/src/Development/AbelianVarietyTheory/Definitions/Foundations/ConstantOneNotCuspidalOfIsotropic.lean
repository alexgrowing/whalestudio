import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant

noncomputable section

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal Pointwise

namespace GlobalTheory.Cusp.Model

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] [T2Space G] {Γ N : Subgroup G} [DiscreteTopology Γ] {μ : Measure G}

theorem exists_lintegral_compact_le [μ.IsMulLeftInvariant] {C : Set G} (hC : IsCompact C) :
    ∃ m : ℕ, ∀ ψ : G → ℂ, LeftInv Γ ψ → Continuous ψ →
      ∫⁻ x in C, ‖ψ x‖ₑ ∂μ ≤ m * ∫⁻ q, ‖descend Γ ψ q‖ₑ ∂quotMeasure Γ μ := by
  have hT := finite_mem_compact (Γ := Γ) (hC.mul hC.inv)
  refine ⟨hT.toFinset.card, fun ψ hl hc => ?_⟩
  rw [← lintegral_indicator hC.measurableSet, lintegral_eq_lintegral_tsum (Γ := Γ)
    ((hc.enorm.measurable.indicator hC.measurableSet).aemeasurable),
    ← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)]
  refine lintegral_mono fun q => ?_
  change _ ≤ _ * ‖ψ q.out‖ₑ
  generalize q.out = x
  by_cases h : ∃ γ₀ : Γ, (γ₀ : G) * x ∈ C
  · obtain ⟨γ₀, h0⟩ := h
    rw [← (Equiv.mulRight γ₀).tsum_eq, tsum_eq_sum (s := hT.toFinset) fun δ hδ => indicator_of_notMem (fun h1 => hδ
      (hT.mem_toFinset.2 ⟨_, h1, _, inv_mem_inv.2 h0, by simp [mul_assoc]⟩)) _, ← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun δ _ => (indicator_le_self _ _ _).trans (le_of_eq ?_)
    exact congrArg _ (hl _ (Subtype.property _) x)
  · push Not at h
    simp [indicator_of_notMem (h _)]

theorem exists_measure_le [LocallyCompactSpace N] [μ.IsMulLeftInvariant] [SFinite μ] (hc : Cocompact Γ N) {U : Set G}
    (hU : IsCompact U) : ∃ m : ℕ, ∀ ψ : G → ℂ, LeftInv Γ ψ → Continuous ψ → (∀ x, constTermOn Γ N ψ x = 1) →
      μ U ≤ m * ∫⁻ q, ‖descend Γ ψ q‖ₑ ∂quotMeasure Γ μ := by
  have := hc.isProbabilityMeasure
  obtain ⟨K, hK, hs⟩ := id hc
  have hKU : IsCompact ((Subtype.val '' K) * U) := (hK.image continuous_subtype_val).mul hU
  obtain ⟨m, hm⟩ := exists_lintegral_compact_le (Γ := Γ) (μ := μ) hKU
  refine ⟨m, fun ψ hl hψ h1 => le_trans ?_ (hm ψ hl hψ)⟩
  have e : ∀ (q : Quot (Γ.subgroupOf N)) (x : G), ψ ((q.out : N) * x) = ψ ((sec _ q : N) * x) := fun q x =>
    ((leftInv_integrand (N := N) hl x) _ (existsUnique_stdDom _ q.out).choose.2 q.out).symm
  have hmeas : Measurable fun p : G × Quot (Γ.subgroupOf N) => ‖ψ ((p.2.out : N) * p.1)‖ₑ := by
    simp only [e]
    exact hψ.enorm.measurable.comp ((measurable_subtype_coe.comp
      (measurableEmbedding_sec.measurable.comp measurable_snd)).mul measurable_fst)
  calc μ U = ∫⁻ _ in U, 1 ∂μ := by simp
    _ ≤ ∫⁻ x in U, ∫⁻ q, ‖ψ ((q.out : N) * x)‖ₑ ∂probMeasure Γ N ∂μ := lintegral_mono fun x => by
      have := enorm_integral_le_lintegral_enorm (μ := probMeasure Γ N) fun q => ψ ((q.out : N) * x)
      rwa [show ∫ q, ψ ((q.out : N) * x) ∂probMeasure Γ N = 1 from h1 x, enorm_one] at this
    _ = ∫⁻ q, ∫⁻ x in U, ‖ψ ((q.out : N) * x)‖ₑ ∂μ ∂probMeasure Γ N := lintegral_lintegral_swap hmeas.aemeasurable
    _ ≤ ∫⁻ _, ∫⁻ x in (Subtype.val '' K) * U, ‖ψ x‖ₑ ∂μ ∂probMeasure Γ N := lintegral_mono fun q => by
      obtain ⟨γ, hγ, hk⟩ := hs q.out
      have e2 : ∀ x, ψ ((q.out : N) * x) = ψ ((γ * q.out : N) * x) := fun x =>
        ((leftInv_integrand (N := N) hl x) _ hγ q.out).symm
      simp only [e2]
      generalize γ * q.out = k at hk
      rw [← (measurePreserving_mul_left μ (k : G)).setLIntegral_comp_preimage_emb (measurableEmbedding_mulLeft _)
        (fun x => ‖ψ x‖ₑ) (Subtype.val '' K * U)]
      exact lintegral_mono_set fun x hx => mul_mem_mul (mem_image_of_mem _ hk) hx
    _ = _ := by simp

end General

section Adelic

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.Mem.Th CuspDecay.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure]

variable (V) in

def constantOneDividedPowerChartLift : DividedPowerChartLift V μ := (memL2_const (Γ := GQ V) (μ := μ) 1).toL2

theorem constant_one_L2_ne_zero : constantOneDividedPowerChartLift V μ ≠ 0 := fun h => by
  have h1 := (memL2_const (Γ := GQ V) (μ := μ) 1).coeFn_toL2
  rw [show (memL2_const (Γ := GQ V) (μ := μ) 1).toL2 = 0 from h] at h1
  obtain ⟨q, hq⟩ := ((Lp.coeFn_zero ℂ 2 _).symm.trans h1).exists
  exact zero_ne_one hq

theorem constant_one_not_cuspidal_of_isotropic (h : 0 < wittIndex V) : constantOneDividedPowerChartLift V μ ∉ L2cusp V μ := by
  obtain ⟨W, hW⟩ := wittIndex_pos_iff.1 h
  have hc := cocompact_single hW
  have : T2Space (GA D V) := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
    infer_instance
  obtain ⟨U, hU, hU1⟩ := exists_compact_mem_nhds (1 : GA D V)
  obtain ⟨m, hm⟩ := exists_measure_le (μ := μ) hc hU
  let c : ℝ≥0∞ := quotMeasure (GQ V) μ univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)
  have hc' : c ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _)
  have hcl : IsClosed {F : DividedPowerChartLift V μ | μ U ≤ (m * c) * ‖constantOneDividedPowerChartLift V μ - F‖ₑ} :=
    isClosed_le continuous_const ((ENNReal.continuous_const_mul (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hc')).comp
      (continuous_const.sub continuous_id).enorm)
  intro h1
  have h2 : μ U ≤ (m * c) * ‖constantOneDividedPowerChartLift V μ - constantOneDividedPowerChartLift V μ‖ₑ := by
    refine closure_minimal (s := (cuspContinuousL2 V μ : Set (DividedPowerChartLift V μ))) ?_ hcl h1
    rintro F ⟨φ, hφ, e⟩
    have hl : LeftInv (GQ V) ((fun _ => 1) + (-1 : ℂ) • φ) := fun γ hγ g => by simp [hφ.2.1 γ hγ g]
    refine (hm _ hl (continuous_const.add (hφ.1.const_smul _)) fun x => ?_).trans ?_
    · rw [hc.constTermOn_add (fun _ _ _ => rfl) continuous_const (fun γ hγ g => by simp [hφ.2.1 γ hγ g])
        (hφ.1.const_smul _), hc.constTermOn_const, constTermOn_smul,
        show constTermOn _ _ φ x = 0 from congrFun ((isCuspFun_iff hφ.2.1).1 hφ.2.2 W hW) x]
      simp
    · rw [mul_assoc, mul_comm c, Lp.enorm_def]
      gcongr
      refine le_trans (le_of_eq ?_) (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) one_le_two (Lp.aestronglyMeasurable _))
      rw [eLpNorm_one_eq_lintegral_enorm]
      refine lintegral_congr_ae ?_
      have e' : ∀ᵐ q ∂quotMeasure (GQ V) μ, F q = descend (GQ V) φ q :=
        ae_quotMeasure_iff.2 (e.mono fun g hg => hg.trans (hφ.2.1.descend_mk g).symm)
      filter_upwards [e', Lp.coeFn_sub (constantOneDividedPowerChartLift V μ) F, (memL2_const (Γ := GQ V) (μ := μ) 1).coeFn_toL2] with q a b d
      rw [b, Pi.sub_apply, a, show constantOneDividedPowerChartLift V μ q = _ from d]
      simp [AutomorphicL2Unitary.descend, sub_eq_add_neg]
  simp only [sub_self, enorm_zero, mul_zero, nonpos_iff_eq_zero] at h2
  exact (Measure.measure_pos_of_mem_nhds μ hU1).ne' h2

theorem constant_one_cuspidal_iff_anisotropic : constantOneDividedPowerChartLift V μ ∈ L2cusp V μ ↔ wittIndex V = 0 :=
  ⟨fun h => by_contra fun h0 => constant_one_not_cuspidal_of_isotropic μ (Nat.pos_of_ne_zero h0) h, fun h => toL2_mem_cuspidal _
    ⟨continuous_const, fun _ _ _ => rfl, fun r C hC => absurd hC (wittIndex_eq_zero_iff_isAniso.1 h r C)⟩⟩

theorem L2cusp_plane_ne_top (μ : Measure (GA D (plane D))) [μ.IsHaarMeasure] : L2cusp (plane D) μ ≠ ⊤ := fun h =>
  constant_one_not_cuspidal_of_isotropic μ (by rw [wittIndex_plane]; exact one_pos) (h ▸ Submodule.mem_top)

theorem L2cusp_ne_bot (h : wittIndex V = 0) : L2cusp V μ ≠ ⊥ := fun e =>
  constant_one_L2_ne_zero μ ((Submodule.mem_bot ℂ).1 (e ▸ (constant_one_cuspidal_iff_anisotropic μ).2 h))

theorem wittIndex_line (D : D7) : wittIndex (line D) = 0 := by
  have h : 2 * wittIndex (line D) ≤ 1 := two_mul_wittIndex_le (line D)
  omega

omit [μ.IsHaarMeasure] in

theorem isCuspAE_of_aniso (h : wittIndex V = 0) (F : DividedPowerChartLift V μ) : IsCuspAE V μ F := fun 𝔉 h' =>
  absurd (exists_proper_iff.1 ⟨𝔉, h'⟩) (by omega)

theorem rank_minusHyp_plane (D : D7) : (minusHyp (plane D) 1 (wittIndex_plane D).ge).rank = 0 := by
  have h : _ + 2 * 1 = 2 := rank_minusHyp (wittIndex_plane D).ge
  omega

end Adelic

section Four

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def four (D : D7) : HSp D := Examples₂.stdSpace Examples₂.star_isIntegral 4 ![false, false, true, true] 2 2

theorem isIsoSub_four (D : D7) :
    IsIsoSub (four D) (i := 2) (!![1, 0; 0, 1; 1, 0; 0, 1] : Matrix (Fin 4) (Fin 2) D.host.E) := by
  refine ⟨?_, ?_⟩
  · refine Fintype.linearIndependent_iff.2 fun g h => ?_
    have h' : ∑ i : Fin 2, g i • (!![1, 0; 0, 1; 1, 0; 0, 1] : Matrix (Fin 4) (Fin 2) D.host.E).transpose i =
      (0 : Fin 4 → D.host.E) := h
    have h0 := congrFun h' 0
    have h1 := congrFun h' 1
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · simpa [Fin.sum_univ_two] using h0
    · simpa [Fin.sum_univ_two] using h1
  · have hg : ∀ i j : Fin 4, (four D).gram i j =
        if i = j then (Examples₂.sgn (![false, false, true, true] i) : D.host.E) else 0 :=
      Examples₂.stdSpace_gram_apply Examples₂.star_isIntegral 4 ![false, false, true, true] 2 2
    funext a b
    change ∑ j : Fin 4, (∑ i : Fin 4, D.sp.cm.sig ((!![1, 0; 0, 1; 1, 0; 0, 1] : Matrix (Fin 4) (Fin 2) D.host.E) i a) *
      (four D).gram i j) * (!![1, 0; 0, 1; 1, 0; 0, 1] : Matrix (Fin 4) (Fin 2) D.host.E) j b = 0
    fin_cases a <;> fin_cases b <;> simp [Fin.sum_univ_four, hg, Examples₂.sgn]

theorem k_columnFlag_four (D : D7) : (columnFlag (isIsoSub_four D)).k = 2 := rfl

theorem wittIndex_four (D : D7) : wittIndex (four D) = 2 := by
  have h1 : 2 * wittIndex (four D) ≤ 4 := two_mul_wittIndex_le (four D)
  have h2 : 2 ≤ wittIndex (four D) := (columnFlag (isIsoSub_four D)).k_le_wittIndex
  omega

end Four

end GlobalTheory.Cusp.Model

end
