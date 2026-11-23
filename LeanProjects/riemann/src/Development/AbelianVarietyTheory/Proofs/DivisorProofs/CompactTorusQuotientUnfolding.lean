import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordMeasure
open MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace GlobalTheory.ParabolicCoord

theorem map_mul_right_haar_of_compact {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [SecondCountableTopology K] [T2Space K] [MeasurableSpace K] [BorelSpace K]
    (μK : Measure K) [μK.IsHaarMeasure] (k : K) :
    μK.map (fun x => x * k) = μK := by
  haveI : (μK.map (· * k)).IsHaarMeasure := Measure.isHaarMeasure_map_mul_right μK k
  set C : ℝ≥0 := Measure.haarScalarFactor (μK.map (· * k)) μK
  have hC : μK.map (· * k) = C • μK := Measure.isMulLeftInvariant_eq_smul _ _
  have hmeas : Measurable (fun x : K => x * k) := measurable_mul_const k
  suffices h1 : C = 1 by rw [hC, h1, one_smul]
  have h2 : C * μK Set.univ = 1 * μK Set.univ := by
    rw [one_mul, ← smul_eq_mul, ← ENNReal.smul_def, ← Measure.smul_apply, ← hC,
      Measure.map_apply hmeas .univ, Set.preimage_univ]
  rwa [ENNReal.mul_left_inj (NeZero.ne _) (measure_ne_top _ _), ENNReal.coe_eq_one] at h2

theorem coordMeasure_map_mul_right : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [SecondCountableTopology K]
    [T2Space K] [MeasurableSpace K] [BorelSpace K]
    (T : Type) [CommGroup T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [SecondCountableTopology T]
    [T2Space T] [MeasurableSpace T] [BorelSpace T]
    (Q : Subgroup G) (κ : K →* G) (m : T →* G) (δ : T →* ℝ≥0) (μK : Measure K) (μT : Measure T) (μQ : Measure Q),
    IsClosed (Q : Set G) → Continuous κ → Topology.IsClosedEmbedding m → Continuous δ → μK.IsHaarMeasure → μT.IsHaarMeasure → μQ.IsHaarMeasure →
    ∀ k, (GlobalTheory.ParabolicCoord.coordMeasure Q κ m δ μQ μT μK).map (fun x => x * κ k) = GlobalTheory.ParabolicCoord.coordMeasure Q κ m δ μQ μT μK := by
  intro G _ _ _ _ _ _ _ _ K _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ Q κ m δ μK μT μQ hQ hκ hm hδ _ _ _ k
  haveI : LocallyCompactSpace Q := hQ.locallyCompactSpace
  haveI : SecondCountableTopology Q := TopologicalSpace.Subtype.secondCountableTopology (Q : Set G)
  haveI : SigmaCompactSpace Q := inferInstance
  haveI : IsFiniteMeasureOnCompacts μQ := inferInstance
  haveI : SigmaFinite μQ := inferInstance
  haveI : SigmaFinite μT := inferInstance
  haveI : SigmaFinite μK := inferInstance
  haveI : SigmaFinite (μT.withDensity fun t => ((δ t : ℝ≥0) : ℝ≥0∞)) :=
    SigmaFinite.withDensity_of_ne_top' fun _ => ENNReal.coe_ne_top
  have hf : Measurable (fun p : K × T × Q => (p.2.2 : G) * (m p.2.1)⁻¹ * κ p.1) := by
    have h1 : Measurable (fun p : K × T × Q => (p.2.2 : G)) :=
      measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)
    have h2 : Measurable (fun p : K × T × Q => m p.2.1) :=
      hm.continuous.measurable.comp (measurable_fst.comp measurable_snd)
    have h3 : Measurable (fun p : K × T × Q => κ p.1) := hκ.measurable.comp measurable_fst
    exact (h1.mul h2.inv).mul h3
  unfold coordMeasure
  rw [Measure.map_map (measurable_mul_const _) hf]
  have hcomp : (fun x : G => x * κ k) ∘ (fun p : K × T × Q => (p.2.2 : G) * (m p.2.1)⁻¹ * κ p.1)
      = (fun p : K × T × Q => (p.2.2 : G) * (m p.2.1)⁻¹ * κ p.1) ∘ Prod.map (fun x : K => x * k) id := by
    funext p; simp [mul_assoc, map_mul]
  rw [hcomp, ← Measure.map_map hf ((measurable_mul_const k).prodMap measurable_id),
    ← Measure.map_prod_map μK _ (measurable_mul_const k) measurable_id,
    map_mul_right_haar_of_compact, Measure.map_id]

end GlobalTheory.ParabolicCoord
