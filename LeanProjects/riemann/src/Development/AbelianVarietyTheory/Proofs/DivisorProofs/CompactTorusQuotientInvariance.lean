import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordMeasure
open MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace GlobalTheory.ParabolicCoord

theorem map_withDensity_mul_right_inv {T : Type} [CommGroup T] [MeasurableSpace T]
    [MeasurableMul T] [MeasurableInv T] (μT : Measure T) [μT.IsMulRightInvariant]
    (δ : T →* ℝ≥0) (hδ : Measurable δ) (s : T) :
    (μT.withDensity fun t => ((δ t : ℝ≥0) : ℝ≥0∞)).map (fun t => t * s⁻¹)
      = ((δ s : ℝ≥0) : ℝ≥0∞) • μT.withDensity fun t => ((δ t : ℝ≥0) : ℝ≥0∞) := by
  have hd : Measurable fun t => ((δ t : ℝ≥0) : ℝ≥0∞) := hδ.coe_nnreal_ennreal
  ext A hA
  have hφ : Measurable fun t : T => t * s⁻¹ := measurable_mul_const _
  rw [Measure.map_apply hφ hA, withDensity_apply _ (hφ hA), Measure.smul_apply,
    withDensity_apply _ hA, smul_eq_mul, ← lintegral_indicator (hφ hA),
    ← lintegral_indicator hA, ← lintegral_const_mul _ (hd.indicator hA)]
  rw [← lintegral_mul_right_eq_self _ s]
  congr 1
  ext u
  by_cases hu : u ∈ A
  · have : u * s ∈ (fun t => t * s⁻¹) ⁻¹' A := by simpa using hu
    rw [Set.indicator_of_mem this, Set.indicator_of_mem hu, map_mul]
    push_cast; ring
  · have : u * s ∉ (fun t => t * s⁻¹) ⁻¹' A := by simpa using hu
    rw [Set.indicator_of_notMem this, Set.indicator_of_notMem hu, mul_zero]

end GlobalTheory.ParabolicCoord

namespace GlobalTheory.ParabolicCoord

theorem coordMeasure_map_mul_left_m :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [SecondCountableTopology K]
    [T2Space K] [MeasurableSpace K] [BorelSpace K]
    (T : Type) [CommGroup T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [SecondCountableTopology T]
    [T2Space T] [MeasurableSpace T] [BorelSpace T]
    (Q : Subgroup G) (κ : K →* G) (m : T →* G) (δ : T →* ℝ≥0) (μK : Measure K) (μT : Measure T) (μQ : Measure Q),
    IsClosed (Q : Set G) → Continuous κ → Topology.IsClosedEmbedding m → Continuous δ → μK.IsHaarMeasure → μT.IsHaarMeasure → μQ.IsHaarMeasure →
    ∀ hn : (∀ t, ∀ q ∈ Q, (m t)⁻¹ * q * m t ∈ Q),
    (∀ μ : Measure Q, μ.IsHaarMeasure → ∀ t, μ.map (fun q : Q => (⟨(m t)⁻¹ * q * m t, hn t q q.2⟩ : Q)) = δ t • μ) →
    ∀ s, (GlobalTheory.ParabolicCoord.coordMeasure Q κ m δ μQ μT μK).map (fun x => m s * x) = GlobalTheory.ParabolicCoord.coordMeasure Q κ m δ μQ μT μK := by
  intro G _ _ _ _ _ _ _ _ K _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ Q κ m δ μK μT μQ hQ hκ hm hδ hμK hμT hμQ hn hmod s
  haveI : LocallyCompactSpace Q := hQ.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hmc : Continuous m := hm.continuous
  haveI : SecondCountableTopology Q := TopologicalSpace.secondCountableTopology_induced _ G Subtype.val
  haveI : SigmaCompactSpace Q := inferInstance
  haveI : SigmaFinite μQ := inferInstance
  haveI : SigmaFinite μT := inferInstance
  have hcm := hmod μQ hμQ s⁻¹
  have hcc : Continuous (fun q : Q => (⟨(m s⁻¹)⁻¹ * q * m s⁻¹, hn s⁻¹ q q.2⟩ : Q)) :=
    Continuous.subtype_mk (by fun_prop) _
  have hF : Measurable (fun p : K × (T × Q) => (p.2.2 : G) * (m p.2.1)⁻¹ * κ p.1) := by
    apply Continuous.measurable; fun_prop
  have hφ : Measurable fun t : T => t * s⁻¹ := measurable_mul_const _
  have hΦ : Measurable (Prod.map (id : K → K) (Prod.map (fun t : T => t * s⁻¹)
      (fun q : Q => (⟨(m s⁻¹)⁻¹ * q * m s⁻¹, hn s⁻¹ q q.2⟩ : Q)))) :=
    measurable_id.prodMap (hφ.prodMap hcc.measurable)
  have hLF : (fun x => m s * x) ∘ (fun p : K × (T × Q) => (p.2.2 : G) * (m p.2.1)⁻¹ * κ p.1)
      = (fun p : K × (T × Q) => (p.2.2 : G) * (m p.2.1)⁻¹ * κ p.1) ∘
        Prod.map (id : K → K) (Prod.map (fun t : T => t * s⁻¹)
          (fun q : Q => (⟨(m s⁻¹)⁻¹ * q * m s⁻¹, hn s⁻¹ q q.2⟩ : Q))) := by
    funext p
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id, map_mul, map_inv, inv_inv]
    group
  have hδm : Measurable δ := hδ.measurable
  unfold coordMeasure
  rw [Measure.map_map (measurable_const_mul _) hF, hLF, ← Measure.map_map hF hΦ]
  congr 1
  rw [← Measure.map_prod_map _ _ measurable_id (hφ.prodMap hcc.measurable), Measure.map_id,
    ← Measure.map_prod_map _ _ hφ hcc.measurable, hcm, map_withDensity_mul_right_inv μT δ hδm s,
    Measure.prod_smul_left, Measure.prod_smul_right, Measure.prod_smul_right, Measure.prod_smul_right,
    ENNReal.smul_def (δ s⁻¹), smul_smul,
    ← ENNReal.coe_mul, ← map_mul, mul_inv_cancel, map_one, ENNReal.coe_one, one_smul]

end GlobalTheory.ParabolicCoord
