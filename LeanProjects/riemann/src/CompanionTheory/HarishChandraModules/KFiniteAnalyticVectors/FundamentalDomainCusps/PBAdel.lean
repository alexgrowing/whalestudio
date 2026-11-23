import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.ShortIsot
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AdelClassFin
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.IwasawaBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.DensRat

open MeasureTheory Topology Filter Set Matrix NumberField
open scoped ENNReal Pointwise InnerProductSpace

noncomputable section

namespace CompanionTheory.D.gk.RF

open Formalism.MainNotions.S Formalism.L2.SG.ProjRows Formalism.MainNotions.LeviCoordinates

theorem exists_GF (I : AutInst) (x : I.Gf) (hx : x ∈ PI.AdelClassFin.GFf I) : ∃ g : I.Ginf, (g, x) ∈ I.GFset := by
  obtain ⟨γ, hγ, h⟩ := hx
  exact ⟨fun v => Formalism.L2.S.S7.DensRat.ratReal I γ hγ v, γ, hγ, fun _ => rfl, h⟩

theorem adelic_cusp_of_infinite_cusp : CuspInf → CongK → CuspAdel := by
  intro hCI hCK I μf _ _ Γ hΓ Kp hKo hKc ph hph hconv U hU
  have : SecondCountableTopology I.Gf := rr_secondCountable I μf
  have : (I.muA μf).IsMulLeftInvariant := rr_muA_left I μf
  have : T2Space I.Gf := Formalism.L2.SG.Pf.finite_adeles_group_t2 I
  have hmem : ∀ {g : I.GA}, g ∈ I.GFset → g ∈ Γ := fun h => by rw [← SetLike.mem_coe, hΓ]; exact h
  obtain ⟨S, hS⟩ := _root_.adelic_class_set_finite I Kp hKo
  have hU' : (fun g : I.Ginf => ((g, 1) : I.GA)) ⁻¹' U ∈ 𝓝 1 :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds hU
  have hs : ∀ s : I.Gf, ∃ M : ℕ, 1 ≤ M ∧ ∀ g ∈ GamSet I M, ∃ x, s⁻¹ * x * s ∈ Kp ∧ (g, x) ∈ I.GFset := fun s =>
    hCK I ((fun x => s⁻¹ * x * s) ⁻¹' Kp) ((hKo.preimage (by fun_prop)).mem_nhds (by simp))
  choose M hM hMK using hs
  choose C hC hCy using fun s => hCI I (M s) (hM s) ph hph hconv _ hU'
  refine ⟨⋃ s ∈ S, C s ×ˢ ((fun k => s * k) '' Kp), S.isCompact_biUnion fun s _ =>
    (hC s).prod (hKc.image (continuous_const.mul continuous_id)), fun x => ?_⟩
  obtain ⟨γf, hγf, s, hsS, k, hk, hx⟩ := hS x.2
  obtain ⟨g₀, hg₀⟩ := exists_GF I γf hγf
  obtain ⟨y, hxe⟩ : ∃ y : I.Ginf, x = (g₀, γf) * (y, s * k) :=
    ⟨g₀⁻¹ * x.1, Prod.ext (by simp) (by simp [hx, mul_assoc])⟩
  generalize ((g₀, γf) : I.GA) = γ₀ at hxe hg₀
  rcases hCy s y with ⟨γ, hγ, hγy⟩ | ⟨ν, hν, hνU, hv⟩
  · obtain ⟨xf, hxf, hGF⟩ := hMK s γ hγ
    refine Or.inl ⟨(γ, xf) * γ₀⁻¹, Γ.mul_mem (hmem hGF) (Γ.inv_mem (hmem hg₀)), mem_iUnion₂.2 ⟨s, hsS, ?_⟩⟩
    rw [hxe, mul_assoc, inv_mul_cancel_left]
    exact ⟨hγy, s⁻¹ * xf * s * k, Kp.mul_mem hxf hk, by simp [mul_assoc]⟩
  right
  let j : I.Ginf → I.GA := fun m => γ₀ * (m, 1) * γ₀⁻¹
  have hjE : MeasurableEmbedding j :=
    (measurableEmbedding_mulRight γ₀⁻¹).comp ((measurableEmbedding_mulLeft γ₀).comp
      (measurableEmbedding_prod_mk_right 1))
  refine ⟨ν.map j, Measure.isProbabilityMeasure_map hjE.measurable.aemeasurable, hjE.ae_map_iff.2 (hνU.mono fun m hm => ?_),
    fun h hh z hz => ?_⟩
  · have : x⁻¹ * j m * x = (y⁻¹ * m * y, 1) := by
      rw [hxe]
      refine Prod.ext ?_ ?_ <;> simp [j, mul_assoc]
    rw [this]
    exact hm
  have hK0 : μf Kp ≠ 0 := (hKo.measure_pos μf ⟨1, Kp.one_mem⟩).ne'
  have hK1 : μf Kp ≠ ∞ := hKc.measure_lt_top.ne
  obtain ⟨hhc, B, hB⟩ := hh.1
  have hright : ∀ k ∈ Kp, ∀ g f, h (g, f * k) = h (g, f) := fun k hk g f => by
    rw [hh.2.2 (g, f * k), hh.2.2 (g, f),
      ← integral_mul_left_eq_self (fun w => phK I μf ph Kp w * h ((g, f) * w)) ((1, k) : I.GA)]
    congr 1
    funext w
    have e1 : phK I μf ph Kp ((1, k) * w) = phK I μf ph Kp w := by
      simp only [phK, Prod.fst_mul, Prod.snd_mul, one_mul]
      congr 1
      by_cases hw : w.2 ∈ Kp
      · rw [indicator_of_mem (show w.2 ∈ (Kp : Set I.Gf) from hw),
          indicator_of_mem (show k * w.2 ∈ (Kp : Set I.Gf) from Kp.mul_mem hk hw)]
      · rw [indicator_of_notMem (show w.2 ∉ (Kp : Set I.Gf) from hw), indicator_of_notMem
          (show k * w.2 ∉ (Kp : Set I.Gf) from fun h => hw ((Kp.mul_mem_cancel_left hk).1 h))]
    rw [e1, ← mul_assoc ((g, f) : I.GA), show ((g, f) : I.GA) * (1, k) = (g, f * k) by simp]
  have hind : Integrable ((Kp : Set I.Gf).indicator fun _ => (((μf Kp).toReal⁻¹ : ℝ) : ℂ)) μf :=
    (integrable_indicator_iff hKo.measurableSet).2 (integrableOn_const hK1)
  have h0 := hv (fun g => h (g, s)) ⟨hhc.comp (by fun_prop), B, fun _ => hB _⟩
    (fun γ hγ g => by
      obtain ⟨xf, hxf, hGF⟩ := hMK s γ hγ
      have := hh.2.1 _ (hmem hGF) (g, s)
      rw [Prod.mk_mul_mk, show xf * s = s * (s⁻¹ * xf * s) by group, hright _ hxf] at this
      exact this)
    (fun g => by
      have e1 : (fun w : I.GA => phK I μf ph Kp w * h ((g, s) * w)) = fun w => (ph w.1 * h (g * w.1, s)) *
          (Kp : Set I.Gf).indicator (fun _ => (((μf Kp).toReal⁻¹ : ℝ) : ℂ)) w.2 := by
        funext w
        by_cases hw : w.2 ∈ Kp
        · have : h ((g, s) * w) = h (g * w.1, s) := hright _ hw _ _
          rw [this, phK]; ring
        · simp only [phK, indicator_of_notMem (show w.2 ∉ (Kp : Set I.Gf) from hw), mul_zero, zero_mul]
      rw [hh.2.2 (g, s), e1]
      refine (integral_prod_mul (μ := muInf I) (ν := μf) (fun z => ph z * h (g * z, s)) _).trans ?_
      rw [integral_indicator_const _ hKo.measurableSet, Measure.real, Complex.real_smul, ← Complex.ofReal_mul,
        mul_inv_cancel₀ (ENNReal.toReal_pos hK0 hK1).ne', Complex.ofReal_one, mul_one]) (y * z.1)
  rw [hjE.integral_map, ← h0]
  congr 1
  funext m
  have : j m * x * z = γ₀ * (m * (y * z.1), s * (k * z.2)) := by
    rw [hxe]
    refine Prod.ext ?_ ?_ <;> simp [j, mul_assoc]
  rw [this, hh.2.1 _ (hmem hg₀), hright _ (Kp.mul_mem hk hz)]

theorem convolution_operator_representation : ConvRep := by
  intro I μf _ _ fund hfund R hR φ₀ T hT Fv ⟨M, hM⟩
  have : SecondCountableTopology I.Gf := rr_secondCountable I μf
  have : (I.muA μf).IsMulLeftInvariant := rr_muA_left I μf
  have : (I.muA μf).IsMulRightInvariant := Formalism.L2.S.S7.IwasawaBase.muA_right I μf
  have : SigmaFinite (I.muA μf) := rr_muA_sigmaFinite I μf
  set μ := I.muA μf
  have hFD := rr_FD_of I μf fund hfund
  obtain ⟨r, hrm, hr⟩ := rr_exists_meas_rep hFD
  let f₀ := (Lp.aestronglyMeasurable Fv).mk
  have hf₀ : Measurable f₀ := (Lp.aestronglyMeasurable Fv).stronglyMeasurable_mk.measurable
  let f : I.GA → ℂ := {x | ‖f₀ x‖ ≤ M}.indicator f₀
  have hf : Measurable f := hf₀.indicator (measurableSet_le hf₀.norm measurable_const)
  have hfb : ∀ x, ‖f x‖ ≤ |M| := fun x => by
    by_cases hx : x ∈ {x | ‖f₀ x‖ ≤ M}
    · rw [show f x = f₀ x from indicator_of_mem hx _]; exact hx.trans (le_abs_self M)
    · rw [show f x = 0 from indicator_of_notMem hx _, norm_zero]; exact abs_nonneg M
  have hfe : ∀ᵐ x ∂μ, x ∈ fund → (Fv : I.GA → ℂ) x = f x := by
    rw [← ae_restrict_iff' hfund.1]
    filter_upwards [hM, (Lp.aestronglyMeasurable Fv).ae_eq_mk] with x h1 h2
    rw [show f x = f₀ x from indicator_of_mem (show x ∈ {x | ‖f₀ x‖ ≤ M} from (congrArg norm h2).ge.trans h1) _]
    exact h2
  have hN : ∀ᵐ x ∂μ, x ∉ rr_N (rr_GF I) fund := compl_mem_ae_iff.2 (rr_N_null hFD)
  have hrep : ∀ x, x ∉ rr_N (rr_GF I) fund → I.rep fund x = r x := fun x hx => by
    obtain ⟨γ, h1, h2, h3⟩ := hr x
    rw [h2]; exact rr_rep_eq hFD hx h1 h3
  have hse : ∀ᵐ x ∂μ, I.ext Fv x = f (r x) := by
    have h1 : ∀ᵐ x ∂μ, ∀ γ : rr_GF I, (γ : I.GA) * x ∈ fund → (Fv : I.GA → ℂ) (γ * x) = f (γ * x) :=
      ae_all_iff.2 fun γ => (measurePreserving_mul_left μ (γ : I.GA)).quasiMeasurePreserving.ae hfe
    filter_upwards [h1, hN] with x a b
    obtain ⟨γ, h1, h2, h3⟩ := hr x
    show (Fv : I.GA → ℂ) (I.rep fund x) = _
    rw [hrep x b, h2]
    exact a ⟨γ, h1⟩ h3
  have hs : Measurable fun x => f (r x) := hf.comp hrm
  refine ⟨fun x => f (r x), hs, ⟨_, fun _ => hfb _⟩, fun γ hγ => ?_, ?_⟩
  · filter_upwards [hN] with x hx
    rw [← hrep x hx, ← hrep _ (rr_N_smul (Γ := rr_GF I) hγ hx)]
    exact congrArg f (rr_rep_smul hFD hγ hx)
  have hm2 : Measurable fun p : I.GA × I.GA => f (r (p.1 * p.2)) := hs.comp measurable_mul
  have hI : ∀ A : Set I.GA, (μ.restrict fund) A < ∞ →
      Integrable (fun p : I.GA × I.GA => φ₀ p.2 * f (r (p.1 * p.2))) (((μ.restrict fund).restrict A).prod μ) :=
    fun A hA => by
      have : IsFiniteMeasure ((μ.restrict fund).restrict A) := ⟨by rwa [Measure.restrict_apply_univ]⟩
      exact (hT.1.comp_snd _).mul_bdd hm2.aestronglyMeasurable (Eventually.of_forall fun _ => hfb _)
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun A _ hA => integrableOn_Lp_of_measure_ne_top _ one_le_two hA.ne)
    (fun A _ hA => (hI A hA).integral_prod_left) fun A hAm hA => ?_
  rw [← L2.inner_indicatorConstLp_one hAm hA.ne, hT.2, integral_integral_swap (hI A hA)]
  congr 1
  funext y
  rw [L2.inner_indicatorConstLp_one, integral_const_mul]
  congr 1
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [hR y Fv, ae_restrict_of_ae ((measurePreserving_mul_right μ y).quasiMeasurePreserving.ae hse)]
    with x a b
  rw [a, b]

end CompanionTheory.D.gk.RF
