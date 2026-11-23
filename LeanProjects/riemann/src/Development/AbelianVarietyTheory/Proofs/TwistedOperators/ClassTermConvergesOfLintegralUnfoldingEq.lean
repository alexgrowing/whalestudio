import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
open MeasureTheory Set GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal

namespace GlobalTheory.ClassTerm

theorem hasClassInt_of_lintegral_eq : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (Γ : Subgroup H) [DiscreteTopology Γ] (γ : H), γ ∈ Γ → ∀ (μ : Measure H) (𝓕 : Set H) (ν : Measure (Quot (cent γ))) (a : ℝ≥0∞), a < ⊤ → (∀ G : H → ℝ≥0∞, Measurable G → ∫⁻ x in 𝓕, ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, G (x⁻¹ * δ * x) ∂μ = a * ∫⁻ q, G (q.out⁻¹ * γ * q.out) ∂ν) → ∀ (f : H → ℂ) (c : ℂ), Continuous f → HasCompactSupport f → Integrable (fun q : Quot (cent γ) => f (q.out⁻¹ * γ * q.out)) ν → ∫ q, f (q.out⁻¹ * γ * q.out) ∂ν = c → GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.HasClassInt Γ μ 𝓕 γ f (a.toReal * c) := by
  intro H _ _ _ _ _ _ _ _ Γ _ γ hγ μ 𝓕 ν a ha hL f c hf hfc hint hc
  classical
  have hmemΓ : ∀ δ ∈ GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, δ ∈ Γ := by
    rintro _ ⟨g, hg, rfl⟩
    exact mul_mem (mul_mem (inv_mem hg) hγ) hg
  let ι : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ → Γ := fun δ => ⟨δ, hmemΓ _ δ.2⟩
  have hι : Function.Injective ι := fun a b h => Subtype.ext (congrArg Subtype.val h :)
  haveI : Countable (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ) := hι.countable
  have hcont : ∀ δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, Continuous fun x : H => x⁻¹ * (δ : H) * x := fun δ => by
    fun_prop
  have hfm : Measurable f := hf.measurable
  have hfs : StronglyMeasurable f := hf.stronglyMeasurable

  have hfin : ∀ x, (Function.support fun δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ => f (x⁻¹ * δ * x)).Finite := by
    intro x
    have hC : IsCompact ((fun z => x * z * x⁻¹) '' tsupport f) := hfc.isCompact.image (by fun_prop)
    refine ((finite_mem_compact (Γ := Γ) hC).preimage hι.injOn).subset ?_
    intro δ hδ
    refine ⟨x⁻¹ * δ * x, subset_tsupport f hδ, ?_⟩
    show x * (x⁻¹ * (δ : H) * x) * x⁻¹ = δ
    group
  have hsum : ∀ x, Summable fun δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ => f (x⁻¹ * δ * x) := fun x =>
    summable_of_hasFiniteSupport (hfin x)

  have hem : Measurable (fun q : Quot (cent γ) => q.out⁻¹ * γ * q.out) := by
    have hli : LeftInv (cent γ) (fun x : H => x⁻¹ * γ * x) := by
      intro t ht x
      have hcomm : γ * t = t * γ := Subgroup.mem_centralizer_iff.1 ht γ (Set.mem_singleton γ)
      have h1 : t⁻¹ * γ * t = γ := by rw [mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
      calc (t * x)⁻¹ * γ * (t * x) = x⁻¹ * (t⁻¹ * γ * t) * x := by group
        _ = x⁻¹ * γ * x := by rw [h1]
    exact measurable_descend hli (by fun_prop : Continuous fun x : H => x⁻¹ * γ * x).measurable
  set m1 : Measure H := Measure.sum fun δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ =>
    (μ.restrict 𝓕).map (fun x => x⁻¹ * (δ : H) * x) with hm1
  set m2 : Measure H := a • ν.map (fun q : Quot (cent γ) => q.out⁻¹ * γ * q.out) with hm2
  have hm12 : m1 = m2 := Measure.ext_of_lintegral _ fun G hG => by
    rw [hm1, hm2, lintegral_sum_measure, lintegral_smul_measure, lintegral_map hG hem,
      tsum_congr (fun δ => lintegral_map hG (hcont δ).measurable), smul_eq_mul, ← hL G hG]
    exact (lintegral_tsum (f := fun (δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ) x => G (x⁻¹ * (δ : H) * x))
      (fun δ => (hG.comp (hcont δ).measurable).aemeasurable)).symm
  have hint2 : Integrable f (ν.map fun q : Quot (cent γ) => q.out⁻¹ * γ * q.out) :=
    (integrable_map_measure hfs.aestronglyMeasurable hem.aemeasurable).2 hint
  have hintm2 : Integrable f m2 := hint2.smul_measure ha.ne
  have hintm1 : Integrable f m1 := hm12 ▸ hintm2
  have hval2 : ∫ x, f x ∂m2 = (a.toReal : ℂ) * c := by
    rw [hm2, integral_smul_measure, integral_map hem.aemeasurable hfs.aestronglyMeasurable, hc, Complex.real_smul]
  have hval1 : ∫ x, f x ∂m1 = ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, ∫ x in 𝓕, f (x⁻¹ * δ * x) ∂μ := by
    rw [hm1, integral_sum_measure (hm1 ▸ hintm1)]
    exact tsum_congr fun δ => integral_map (hcont δ).measurable.aemeasurable hfs.aestronglyMeasurable
  have hfinL : ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, ∫⁻ x in 𝓕, ‖f (x⁻¹ * δ * x)‖ₑ ∂μ ≠ ∞ := by
    have h := hintm1.hasFiniteIntegral
    change ∫⁻ x, ‖f x‖ₑ ∂m1 < ∞ at h
    rw [hm1, lintegral_sum_measure] at h
    refine ne_of_lt (lt_of_eq_of_lt (tsum_congr fun δ => ?_) h)
    exact (lintegral_map hfm.enorm (hcont δ).measurable).symm
  have hKm : Measurable (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel Γ γ f) :=
    measurable_of_tendsto_metrizable' (Filter.atTop : Filter (Finset (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ)))
      (f := fun (s : Finset (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ)) x => ∑ δ ∈ s, f (x⁻¹ * (δ : H) * x))
      (fun s => Finset.measurable_sum s fun δ _ => hfm.comp (hcont δ).measurable)
      (tendsto_pi_nhds.2 fun x => (hsum x).hasSum)
  refine ⟨hsum, ⟨hKm.aestronglyMeasurable, ?_⟩, ?_⟩
  · change ∫⁻ x, ‖GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel Γ γ f x‖ₑ ∂μ.restrict 𝓕 < ∞
    calc ∫⁻ x, ‖GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel Γ γ f x‖ₑ ∂μ.restrict 𝓕
        ≤ ∫⁻ x, ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, ‖f (x⁻¹ * δ * x)‖ₑ ∂μ.restrict 𝓕 :=
          lintegral_mono fun x => enorm_tsum_le_tsum_enorm
      _ = ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, ∫⁻ x in 𝓕, ‖f (x⁻¹ * δ * x)‖ₑ ∂μ :=
          lintegral_tsum (fun δ => (hfm.comp (hcont δ).measurable).enorm.aemeasurable)
      _ < ∞ := hfinL.lt_top
  · show ∫ x in 𝓕, ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, f (x⁻¹ * δ * x) ∂μ = _
    rw [integral_tsum (f := fun (δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ) x => f (x⁻¹ * (δ : H) * x)) (fun δ => (hfm.comp (hcont δ).measurable).aestronglyMeasurable) hfinL, ← hval1, hm12, hval2]

end GlobalTheory.ClassTerm
