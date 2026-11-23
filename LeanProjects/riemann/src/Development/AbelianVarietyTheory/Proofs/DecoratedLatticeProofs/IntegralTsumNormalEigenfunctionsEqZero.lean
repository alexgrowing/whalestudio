import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingZeroMeanNormalizedSubgroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarMapMulRightEqOfFiniteFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FundamentalDomainSetIntegralMulRight
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EncardSmulMemLeEncardSmulInterNonempty
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
namespace GlobalTheory.CutSum

open Filter Topology

theorem measurable_tsum_of_summable {X I : Type} [MeasurableSpace X] [Countable I]
    (F : I → X → ℂ) (hF : ∀ i, Measurable (F i)) (hs : ∀ x, Summable fun i => F i x) :
    Measurable fun x => ∑' i, F i x :=
  measurable_of_tendsto_metrizable' (atTop : Filter (Finset I))
    (f := fun s x => ∑ i ∈ s, F i x) (fun s => Finset.measurable_sum s fun i _ => hF i)
    (tendsto_pi_nhds.2 fun x => (hs x).hasSum)

theorem summable_of_tsum_enorm_ne_top {I : Type} (f : I → ℂ) (h : ∑' i, ‖f i‖ₑ ≠ ⊤) :
    Summable f := by
  refine Summable.of_norm ?_
  simp only [enorm_eq_nnnorm] at h
  exact NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 h)

theorem integrableOn_of_enorm_le {X : Type} [MeasurableSpace X] {μ : Measure X} {s : Set X}
    (hs : μ s ≠ ⊤) {φ : X → ℂ} (hφ : Measurable φ) (B : NNReal) (hb : ∀ x, ‖φ x‖ₑ ≤ B) :
    IntegrableOn φ s μ := by
  refine ⟨hφ.aestronglyMeasurable, ?_⟩
  show ∫⁻ x in s, ‖φ x‖ₑ ∂μ < ⊤
  exact (lintegral_mono hb).trans_lt
    ((setLIntegral_const s _).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hs.lt_top))

end GlobalTheory.CutSum

open GlobalTheory.CutSum in

theorem GlobalTheory.CutSum.integral_tsum_eq_zero : ∀ (N : Type) [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N] [SecondCountableTopology N] [T2Space N] [MeasurableSpace N] [BorelSpace N] (ν : Measure N) [ν.IsHaarMeasure] (Γ M : Subgroup N), Countable Γ → DiscreteTopology Γ → M.Normal → IsClosed (M : Set N) → (∃ K : Set M, IsCompact K ∧ ∀ m, ∃ γ ∈ Γ.subgroupOf M, ∃ k ∈ K, m = γ * k) → ∀ 𝓝 : Set N, IsFundamentalDomain Γ 𝓝 ν → ν 𝓝 ≠ ⊤ → ∀ (I C : Type) [Countable I] (κ : I → C) (F : I → N → ℂ), (∀ i, Measurable (F i)) → (∃ B : NNReal, ∀ n, ∑' i, ‖F i n‖ₑ ≤ B) → (∀ γ ∈ Γ, ∀ n, ∑' i, F i (γ * n) = ∑' i, F i n) → (∀ c, ∀ γ ∈ Γ, γ ∈ M → ∀ n, ∑' i : {i // κ i = c}, F i (γ * n) = ∑' i : {i // κ i = c}, F i n) → (∀ c, ∃ u ∈ M, ∃ a : ℂ, a ≠ 1 ∧ ∀ i, κ i = c → ∀ m ∈ M, ∀ n, F i (m * u * n) = a * F i (m * n)) → ∫ n in 𝓝, ∑' i, F i n ∂ν = 0 := by
  intro N _ _ _ _ _ _ _ _ ν _ Γ M hΓc hΓd hMn hMc hK 𝓝 h𝓝 h𝓝fin I C _ cl F hFm hB hΓ hcl heig
  classical
  haveI := hΓd
  haveI : LocallyCompactSpace M := hMc.locallyCompactSpace
  haveI : SecondCountableTopology M := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : BorelSpace M := Subtype.borelSpace _
  obtain ⟨B, hB⟩ := hB

  have hinj : Function.Injective fun γ : Γ.subgroupOf M =>
      (⟨(γ : M), Subgroup.mem_subgroupOf.1 γ.2⟩ : Γ) :=
    fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : Γ => (x : N)) h))
  haveI : Countable (Γ.subgroupOf M) := hinj.countable
  haveI : DiscreteTopology (Γ.subgroupOf M) := DiscreteTopology.of_continuous_injective
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) hinj
  let μM : Measure M := Measure.haar
  obtain ⟨D, -, -, hD⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (Γ.subgroupOf M)
  have hDf : μM D ≠ ⊤ := by
    obtain ⟨K, hKc, hKcov⟩ := hK
    refine ne_top_of_le_ne_top hKc.measure_lt_top.ne
      (GlobalTheory.measure_le_of_isFundamentalDomain_of_ae_covers (hD μM) (D' := K)
        (Filter.Eventually.of_forall fun m => ?_))
    obtain ⟨γ, hγ, k, hk, rfl⟩ := hKcov m
    refine ⟨⟨γ, hγ⟩⁻¹, ?_⟩
    show ((⟨γ, hγ⟩⁻¹ : Γ.subgroupOf M) : M) * (γ * k) ∈ K
    rw [Subgroup.coe_inv, Subgroup.coe_mk, inv_mul_cancel_left]
    exact hk
  have hR : ∀ u : M, μM.map (· * u) = μM :=
    GlobalTheory.haar_map_mul_right_eq_of_fundamentalDomain N Γ M hΓc hMc μM D inferInstance (hD μM) hDf

  have hs : ∀ n, Summable fun i => F i n := fun n =>
    summable_of_tsum_enorm_ne_top _ (ne_top_of_le_ne_top ENNReal.coe_ne_top (hB n))
  let g : I → Set.range cl := Set.rangeFactorization cl
  haveI : Countable (Set.range cl) := (Set.countable_range cl).to_subtype
  let G : Set.range cl → N → ℂ := fun c n => ∑' i : {i // cl i = c.1}, F i n
  have hfib : ∀ c n, ∑' b : ↑(g ⁻¹' {c}), F b n = G c n := fun c n =>
    (Equiv.subtypeEquivRight (fun i => by
      simp [g, Set.rangeFactorization, Subtype.ext_iff])).tsum_eq
      (fun j : {i // cl i = c.1} => F j.1 n)
  have hsplit : ∀ n, ∑' i, F i n = ∑' c, G c n := fun n =>
    (((hs n).hasSum.tsum_fiberwise g).tsum_eq).symm.trans (tsum_congr fun c => hfib c n)
  have hGle : ∀ n, ∑' c, ‖G c n‖ₑ ≤ B := fun n => by
    calc ∑' c, ‖G c n‖ₑ ≤ ∑' c, ∑' b : ↑(g ⁻¹' {c}), ‖F b n‖ₑ :=
          ENNReal.tsum_le_tsum fun c => by rw [← hfib c n]; exact enorm_tsum_le_tsum_enorm
      _ = ∑' i, ‖F i n‖ₑ := ENNReal.tsum_fiberwise (fun i => ‖F i n‖ₑ) g
      _ ≤ B := hB n
  have hGm : ∀ c, Measurable (G c) := fun c =>
    measurable_tsum_of_summable (fun i : {i // cl i = c.1} => F i) (fun i => hFm i)
      (fun n => (hs n).comp_injective Subtype.val_injective)
  have hfm : Measurable fun n => ∑' i, F i n := measurable_tsum_of_summable F hFm hs

  have hzero : ∀ c (h : N), ∫ m in D, G c ((m : N) * h) ∂μM = 0 := by
    intro c h
    obtain ⟨u, huM, a, ha1, hu⟩ := heig c.1
    set φ : M → ℂ := fun m => G c ((m : N) * h) with hφ
    have hφm : Measurable φ := (hGm c).comp (measurable_subtype_coe.mul_const h)
    have hφint : IntegrableOn φ D μM :=
      integrableOn_of_enorm_le hDf hφm B fun m => (ENNReal.le_tsum c).trans (hGle _)
    have hinv : ∀ γ ∈ Γ.subgroupOf M, ∀ m : M, φ (γ * m) = φ m := by
      intro γ hγ m
      show G c (((γ * m : M) : N) * h) = G c ((m : N) * h)
      rw [Subgroup.coe_mul, mul_assoc]
      exact hcl c.1 γ (Subgroup.mem_subgroupOf.1 hγ) γ.2 _
    have hshift : ∀ m : M, φ (m * ⟨u, huM⟩) = a * φ m := by
      intro m
      show G c (((m * ⟨u, huM⟩ : M) : N) * h) = a * G c ((m : N) * h)
      rw [Subgroup.coe_mul, Subgroup.coe_mk]
      show ∑' i : {i // cl i = c.1}, F i ((m : N) * u * h)
        = a * ∑' i : {i // cl i = c.1}, F i ((m : N) * h)
      rw [← tsum_mul_left]
      exact tsum_congr fun i => hu i i.2 m m.2 h
    have key := (GlobalTheory.fundamentalDomain_setIntegral_mul_right (Γ.subgroupOf M) μM D (hD μM)
      ⟨u, huM⟩ (hR _) φ hinv hφint).2
    simp only [hshift, integral_const_mul] at key
    have h2 : (a - 1) * ∫ m in D, φ m ∂μM = 0 := by rw [sub_mul, one_mul, key, sub_self]
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 ha1)

  have hmean : ∀ h : N, ∫ m in D, (∑' i, F i ((m : N) * h)) ∂μM = 0 := by
    intro h
    have hm : ∀ c, Measurable fun m : M => G c ((m : N) * h) := fun c =>
      (hGm c).comp (measurable_subtype_coe.mul_const h)
    simp_rw [hsplit]
    rw [integral_tsum (fun c => (hm c).aestronglyMeasurable) ?_]
    · simp [hzero]
    · rw [← lintegral_tsum (fun c => (hm c).enorm.aemeasurable)]
      refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.coe_ne_top (r := B)) hDf) ?_
      exact (lintegral_mono fun m => hGle _).trans_eq (setLIntegral_const D _)
  have hfin := GlobalTheory.UnfoldNormal.unfold_zero_mean N ν Γ M hΓc hMc
    (fun γ _ n hn => hMn.conj_mem n hn γ) μM D inferInstance (hD μM) hDf
    (fun _ => 1) (fun n => ∑' i, F i n) measurable_const hfm (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) (fun γ hγ n => hΓ γ hγ n) hmean 𝓝 h𝓝
    (integrableOn_of_enorm_le h𝓝fin (measurable_const.mul hfm) B fun n => by
      simpa using enorm_tsum_le_tsum_enorm.trans (hB n))
  simpa using hfin
