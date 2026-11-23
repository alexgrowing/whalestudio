import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixPer

theorem exists_mul_of_mem_sup_range {G H : Type} [Group G] [Group H] (N : Subgroup G) (s : H →* G)
    (hnorm : ∀ n ∈ N, ∀ h, s h * n * (s h)⁻¹ ∈ N) {g : G} (hg : g ∈ N ⊔ s.range) :
    ∃ n ∈ N, ∃ h, g = n * s h := by
  let K : Subgroup G :=
    { carrier := {x | ∃ n ∈ N, ∃ h, x = n * s h}
      one_mem' := ⟨1, N.one_mem, 1, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨n₁, hn₁, h₁, rfl⟩ ⟨n₂, hn₂, h₂, rfl⟩
        refine ⟨n₁ * (s h₁ * n₂ * (s h₁)⁻¹), N.mul_mem hn₁ (hnorm n₂ hn₂ h₁), h₁ * h₂, ?_⟩
        rw [map_mul]
        group
      inv_mem' := by
        rintro _ ⟨n, hn, h, rfl⟩
        refine ⟨s h⁻¹ * n⁻¹ * (s h⁻¹)⁻¹, hnorm n⁻¹ (N.inv_mem hn) h⁻¹, h⁻¹, ?_⟩
        rw [map_inv]
        group }
  have hle : N ⊔ s.range ≤ K := by
    refine sup_le (fun n hn => ⟨n, hn, 1, by simp⟩) ?_
    rintro _ ⟨h, rfl⟩
    exact ⟨1, N.one_mem, h, by simp⟩
  exact hle hg

theorem semiMeas_finite_on_compacts_and_open_pos : ∀ {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (N : Subgroup G) (s : H →* G), IsClosed (N : Set G) → Continuous s → (∀ n ∈ N, ∀ h, s h * n * (s h)⁻¹ ∈ N) → (∃ p : (N ⊔ s.range : Subgroup G) → H, Continuous p ∧ ∀ (h : H) (n : N), p ⟨n.1 * s h, mul_mem (Subgroup.mem_sup_left n.2) (Subgroup.mem_sup_right ⟨h, rfl⟩)⟩ = h) → ∀ (μ : Measure H) (ν : Measure N), μ.IsHaarMeasure → ν.IsHaarMeasure → (∀ h, ν.map (fun n : N => s h * n.1 * (s h)⁻¹) = ν.map Subtype.val) → IsFiniteMeasureOnCompacts (semiMeas N s μ ν) ∧ (semiMeas N s μ ν).IsOpenPosMeasure := by
  intro G H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N s hN hs hnorm hp μ ν hμ hν _
  obtain ⟨p, hpc, hps⟩ := hp
  haveI : LocallyCompactSpace N := hN.locallyCompactSpace
  haveI : SecondCountableTopology N := inferInstanceAs (SecondCountableTopology (N : Set G))
  haveI : IsFiniteMeasureOnCompacts ν := inferInstance
  haveI : IsLocallyFiniteMeasure ν := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : SigmaFinite ν := sigmaFinite_of_locallyFinite
  haveI : μ.IsOpenPosMeasure := inferInstance
  haveI : ν.IsOpenPosMeasure := inferInstance
  haveI : (μ.prod ν).IsOpenPosMeasure := inferInstance

  let φ : H × N → (N ⊔ s.range : Subgroup G) := fun q =>
    ⟨q.2.1 * s q.1, mul_mem (Subgroup.mem_sup_left q.2.2) (Subgroup.mem_sup_right ⟨q.1, rfl⟩)⟩
  have hφc : Continuous φ :=
    ((continuous_subtype_val.comp continuous_snd).mul (hs.comp continuous_fst)).subtype_mk _
  have hmemN : ∀ k : (N ⊔ s.range : Subgroup G), (k : G) * (s (p k))⁻¹ ∈ N := by
    intro k
    obtain ⟨n, hn, h, hk⟩ := exists_mul_of_mem_sup_range N s hnorm k.2
    have hpk : p k = h := by
      have hk' : k = ⟨n * s h, mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨h, rfl⟩)⟩ :=
        Subtype.ext hk
      rw [hk']
      exact hps h ⟨n, hn⟩
    rw [hpk, hk, mul_inv_cancel_right]
    exact hn
  let ψ : (N ⊔ s.range : Subgroup G) → H × N := fun k => (p k, ⟨(k : G) * (s (p k))⁻¹, hmemN k⟩)
  have hψc : Continuous ψ :=
    hpc.prodMk ((continuous_subtype_val.mul (hs.comp hpc).inv).subtype_mk _)
  have hψφ : ∀ q, ψ (φ q) = q := by
    rintro ⟨h, n⟩
    have h1 : p (φ (h, n)) = h := hps h n
    refine Prod.ext h1 (Subtype.ext ?_)
    show (n : G) * s h * (s (p (φ (h, n))))⁻¹ = n
    rw [h1, mul_inv_cancel_right]
  have hφψ : ∀ k, φ (ψ k) = k := by
    intro k
    apply Subtype.ext
    show (k : G) * (s (p k))⁻¹ * s (p k) = k
    rw [inv_mul_cancel_right]
  have hsurj : Function.Surjective φ := fun k => ⟨ψ k, hφψ k⟩
  show IsFiniteMeasureOnCompacts ((μ.prod ν).map φ) ∧ ((μ.prod ν).map φ).IsOpenPosMeasure
  refine ⟨⟨fun C hC => ?_⟩, hφc.isOpenPosMeasure_map hsurj⟩
  rw [Measure.map_apply hφc.measurable hC.measurableSet]
  refine lt_of_le_of_lt (measure_mono ?_) (hC.image hψc).measure_lt_top
  intro q hq
  exact ⟨φ q, hq, hψφ q⟩

end GlobalTheory.MixPer
