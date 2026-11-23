import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CellInt

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

def dcos (R K : Subgroup G) (q : G) : Set G := {g | ∃ r ∈ R, ∃ k ∈ K, g = r * q * k}

theorem dcos_eq_of_mem {R K : Subgroup G} {q h : G} (hh : h ∈ dcos R K q) : dcos R K h = dcos R K q := by
  obtain ⟨r, hr, k, hk, rfl⟩ := hh
  ext g
  constructor
  · rintro ⟨r', hr', k', hk', rfl⟩
    exact ⟨r' * r, R.mul_mem hr' hr, k * k', K.mul_mem hk hk', by group⟩
  · rintro ⟨r', hr', k', hk', rfl⟩
    exact ⟨r' * r⁻¹, R.mul_mem hr' (R.inv_mem hr), k⁻¹ * k', K.mul_mem (K.inv_mem hk) hk', by group⟩

def cellSet (R K : Subgroup G) (q h : G) : Set R := {r | q⁻¹ * ((r : G) * h) ∈ K}

theorem isOpen_cellSet {R K : Subgroup G} (hK : IsOpen (K : Set G)) (q h : G) : IsOpen (cellSet R K q h) :=
  (continuous_const.mul (continuous_subtype_val.mul continuous_const)).isOpen_preimage _ hK

theorem isCompact_cellSet {R K : Subgroup G} (hR : IsClosed (R : Set G)) (hK : IsCompact (K : Set G)) (q h : G) :
    IsCompact (cellSet R K q h) := by
  have h1 : IsCompact ((fun x : G => q⁻¹ * (x * h)) ⁻¹' (K : Set G)) :=
    ((Homeomorph.mulRight h).trans (Homeomorph.mulLeft q⁻¹)).isCompact_preimage.2 hK
  exact hR.isClosedEmbedding_subtypeVal.isCompact_preimage h1

theorem cellSet_of_mem {R K : Subgroup G} {q h : G} (r0 : R) (k0 : G) (hk0 : k0 ∈ K) (hh : h = r0 * q * k0) :
    cellSet R K q h = (fun r => r * r0) ⁻¹' cellSet R K q q := by
  ext r
  simp only [cellSet, Set.mem_preimage, Set.mem_setOf_eq, Subgroup.coe_mul, hh]
  constructor
  · intro hr
    have := K.mul_mem hr (K.inv_mem hk0)
    convert this using 1; group
  · intro hr
    have := K.mul_mem hr hk0
    convert this using 1; group

theorem cellSet_eq_empty {R K : Subgroup G} {q h : G} (hh : h ∉ dcos R K q) : cellSet R K q h = ∅ :=
  Set.eq_empty_of_forall_notMem fun r hr =>
    hh ⟨(r : G)⁻¹, R.inv_mem r.2, q⁻¹ * ((r : G) * h), hr, by group⟩

open Classical in

theorem isQuotientIntegral_indicator_doubleCoset (R K : Subgroup G) (hR : IsClosed (R : Set G)) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) (ρ : Measure R) (μ : Measure G) [ρ.IsHaarMeasure] [ρ.IsInvInvariant]
    [μ.IsHaarMeasure] (q : G) :
    IsQuotIntL1 ρ μ (fun g => if g ∈ dcos R K q then 1 else 0)
      (((μ (K : Set G)).toReal / (ρ (cellSet R K q q)).toReal : ℝ) : ℂ) := by
  classical
  have hRI : ρ.IsMulRightInvariant := by rw [← Measure.inv_eq_self ρ]; infer_instance
  set c : ℂ := ((((ρ (cellSet R K q q)).toReal)⁻¹ : ℝ) : ℂ) with hc
  set A : Set G := (fun x => q⁻¹ * x) ⁻¹' (K : Set G) with hA
  have hAo : IsOpen A := (continuous_const.mul continuous_id).isOpen_preimage _ hKo
  have hAc : IsCompact A := (Homeomorph.mulLeft q⁻¹).isCompact_preimage.2 hKc
  have hAμ : μ A = μ K := measure_preimage_mul μ q⁻¹ _
  have hS0 : ρ (cellSet R K q q) ≠ 0 := (isOpen_cellSet hKo q q).measure_ne_zero ρ ⟨1, by simp [cellSet]⟩
  have hSt : ρ (cellSet R K q q) ≠ ⊤ := ((isCompact_cellSet hR hKc q q).measure_lt_top (μ := ρ)).ne
  have e : ∀ h, (fun r : R => A.indicator (fun _ => c) ((r : G) * h)) = (cellSet R K q h).indicator fun _ => c := by
    intro h; funext r; simp only [Set.indicator_apply, hA, cellSet, Set.mem_preimage, Set.mem_setOf_eq, SetLike.mem_coe]
  refine ⟨A.indicator fun _ => c, ?_, fun h => ?_, fun h => ?_, ?_⟩
  · exact (integrableOn_const hAc.measure_lt_top.ne).integrable_indicator hAo.measurableSet
  · rw [e h]
    exact (integrableOn_const ((isCompact_cellSet hR hKc q h).measure_lt_top (μ := ρ)).ne).integrable_indicator
      (isOpen_cellSet hKo q h).measurableSet
  · rw [e h, integral_indicator (isOpen_cellSet hKo q h).measurableSet, setIntegral_const]
    show (if h ∈ dcos R K q then (1 : ℂ) else 0) = ρ.real (cellSet R K q h) • c
    by_cases hh : h ∈ dcos R K q
    · rw [if_pos hh]
      obtain ⟨r0, hr0, k0, hk0, rfl⟩ := hh
      rw [cellSet_of_mem ⟨r0, hr0⟩ k0 hk0 rfl, measureReal_def, measure_preimage_mul_right, hc, Complex.real_smul,
        ← Complex.ofReal_mul, mul_inv_cancel₀ (ENNReal.toReal_ne_zero.2 ⟨hS0, hSt⟩), Complex.ofReal_one]
    · rw [if_neg hh, cellSet_eq_empty hh]
      simp
  · rw [integral_indicator hAo.measurableSet, setIntegral_const, measureReal_def, hAμ, hc, Complex.real_smul, ← Complex.ofReal_mul, div_eq_mul_inv]

theorem quotient_integral_finset_sum {R : Subgroup G} {ρ : Measure R} {μ : Measure G} {ι : Type} (s : Finset ι)
    (g : ι → G → ℂ) (z : ι → ℂ) (hs : ∀ i ∈ s, IsQuotIntL1 ρ μ (g i) (z i)) :
    IsQuotIntL1 ρ μ (fun h => ∑ i ∈ s, g i h) (∑ i ∈ s, z i) := by
  classical
  revert hs
  refine Finset.induction_on s ?_ ?_
  · intro _
    have e : (fun h => ∑ i ∈ (∅ : Finset ι), g i h) = 0 := by funext h; simp
    rw [e, Finset.sum_empty]
    exact IsQuotIntL1.zero
  · intro a s ha ih hs
    have := (hs a (Finset.mem_insert_self a s)).add (ih fun i hi => hs i (Finset.mem_insert_of_mem hi))
    rw [Finset.sum_insert ha]
    convert this using 1
    funext h
    simp [Finset.sum_insert ha]

end GlobalTheory.CellInt

open GlobalTheory.CellInt in

theorem GlobalTheory.CellInt.quotInt_finiteCells : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (R K : Subgroup G), IsClosed (R : Set G) → IsCompact (K : Set G) → IsOpen (K : Set G) → ∀ (ρ : Measure R) (μ : Measure G), ρ.IsHaarMeasure → ρ.IsInvInvariant → μ.IsHaarMeasure → μ.IsMulRightInvariant → ∀ T : Finset G, ∃ (T' : Finset G) (w : G → ℂ), T' ⊆ T ∧ ∀ f : G → ℂ, (∀ r ∈ R, ∀ g, f (r * g) = f g) → (∀ k ∈ K, ∀ g, f (g * k) = f g) → (∀ g, f g ≠ 0 → ∃ q ∈ T, ∃ r ∈ R, ∃ k ∈ K, g = r * q * k) → IsQuotIntL1 ρ μ f (∑ q ∈ T', w q * f q) := by
  intro G _ _ _ _ _ _ _ _ R K hR hKc hKo ρ μ hρ hρi hμ hμr T
  classical
  obtain ⟨u, hus, hinj, himg⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn (f := dcos R K) (T : Set G)
    (T.image (dcos R K)) (by rw [Finset.coe_image]; exact Set.surjOn_image _ _)
  refine ⟨u, fun q => (((μ (K : Set G)).toReal / (ρ (cellSet R K q q)).toReal : ℝ) : ℂ), Finset.coe_subset.1 hus,
    fun f hfR hfK hsupp => ?_⟩
  have hinv : ∀ q h, h ∈ dcos R K q → f h = f q := by
    rintro q h ⟨r, hr, k, hk, rfl⟩
    rw [mul_assoc, hfR r hr, hfK k hk]
  have key : ∀ h, f h = ∑ q ∈ u, f q * (if h ∈ dcos R K q then 1 else 0) := by
    intro h
    by_cases hex : ∃ q0 ∈ u, h ∈ dcos R K q0
    · obtain ⟨q0, hq0, hh⟩ := hex
      rw [Finset.sum_eq_single q0 (fun q hq hne => ?_) (fun h' => absurd hq0 h'), if_pos hh, mul_one, hinv q0 h hh]
      rw [if_neg, mul_zero]
      intro hq'
      exact hne (hinj hq hq0 ((dcos_eq_of_mem hq').symm.trans (dcos_eq_of_mem hh)))
    · rw [Finset.sum_eq_zero fun q hq => by rw [if_neg fun hh => hex ⟨q, hq, hh⟩, mul_zero]]
      by_contra hne
      obtain ⟨q, hq, r, hr, k, hk, hh⟩ := hsupp h hne
      have hm : dcos R K q ∈ u.image (dcos R K) := himg ▸ Finset.mem_image_of_mem _ hq
      obtain ⟨q', hq', he⟩ := Finset.mem_image.1 hm
      exact hex ⟨q', hq', by rw [he]; exact ⟨r, hr, k, hk, hh⟩⟩
  have hS := quotient_integral_finset_sum u (fun q h => f q * if h ∈ dcos R K q then 1 else 0)
    (fun q => (((μ (K : Set G)).toReal / (ρ (cellSet R K q q)).toReal : ℝ) : ℂ) * f q) fun q _ => by
      have := (isQuotientIntegral_indicator_doubleCoset R K hR hKc hKo ρ μ q).smul (f q)
      convert this using 1
      · funext h; simp [smul_eq_mul]
      · ring
  convert hS using 1
  exact funext key
