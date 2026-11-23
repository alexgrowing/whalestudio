import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.MixPer.semiMeas_isMulLeftInvariant {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (N : Subgroup G) (s : H →* G) (hN : IsClosed (N : Set G)) (hs : Continuous s)
    (hnorm : ∀ n ∈ N, ∀ h, s h * n * (s h)⁻¹ ∈ N)
    (_hp : ∃ p : (N ⊔ s.range : Subgroup G) → H, Continuous p ∧ ∀ (h : H) (n : N),
      p ⟨n.1 * s h, mul_mem (Subgroup.mem_sup_left n.2) (Subgroup.mem_sup_right ⟨h, rfl⟩)⟩ = h)
    (μ : Measure H) (ν : Measure N) (hμ : μ.IsHaarMeasure) (hν : ν.IsHaarMeasure)
    (hc : ∀ h, ν.map (fun n : N => s h * n.1 * (s h)⁻¹) = ν.map Subtype.val) :
    (semiMeas N s μ ν).IsMulLeftInvariant := by
  have := hμ
  have := hν
  have : LocallyCompactSpace N := hN.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set G)
  have : SigmaCompactSpace N := sigmaCompactSpace_of_locallyCompact_secondCountable
  have : SigmaFinite ν := inferInstance
  have : SigmaFinite μ := inferInstance
  have hemb : MeasurableEmbedding (Subtype.val : N → G) :=
    MeasurableEmbedding.subtype_coe hN.measurableSet

  let φ : H × N → (N ⊔ s.range : Subgroup G) := fun p =>
    ⟨p.2.1 * s p.1, mul_mem (Subgroup.mem_sup_left p.2.2) (Subgroup.mem_sup_right ⟨p.1, rfl⟩)⟩
  have hφ : Measurable φ :=
    (Continuous.subtype_mk ((continuous_subtype_val.comp continuous_snd).mul
      (hs.comp continuous_fst)) _).measurable
  have hm : semiMeas N s μ ν = (μ.prod ν).map φ := rfl

  let T : Subgroup G :=
    { carrier := {g | ∃ hg : g ∈ N ⊔ s.range,
        (semiMeas N s μ ν).map (fun x => (⟨g, hg⟩ : (N ⊔ s.range : Subgroup G)) * x) =
          semiMeas N s μ ν}
      one_mem' := by
        refine ⟨one_mem _, ?_⟩
        have e : (fun x : (N ⊔ s.range : Subgroup G) =>
            (⟨1, one_mem _⟩ : (N ⊔ s.range : Subgroup G)) * x) = id := funext fun x => one_mul x
        rw [e, Measure.map_id]
      mul_mem' := by
        rintro a b ⟨ha, ea⟩ ⟨hb, eb⟩
        refine ⟨mul_mem ha hb, ?_⟩
        have e : (fun x : (N ⊔ s.range : Subgroup G) =>
            (⟨a * b, mul_mem ha hb⟩ : (N ⊔ s.range : Subgroup G)) * x) =
            (fun x => (⟨a, ha⟩ : (N ⊔ s.range : Subgroup G)) * x) ∘
              (fun x => (⟨b, hb⟩ : (N ⊔ s.range : Subgroup G)) * x) :=
          funext fun x => mul_assoc (⟨a, ha⟩ : (N ⊔ s.range : Subgroup G)) ⟨b, hb⟩ x
        rw [e, ← Measure.map_map (measurable_const_mul _) (measurable_const_mul _), eb, ea]
      inv_mem' := by
        rintro a ⟨ha, ea⟩
        refine ⟨inv_mem ha, ?_⟩
        conv_lhs => rw [← ea]
        rw [Measure.map_map (measurable_const_mul _) (measurable_const_mul _)]
        have e : ((fun x : (N ⊔ s.range : Subgroup G) =>
            (⟨a⁻¹, inv_mem ha⟩ : (N ⊔ s.range : Subgroup G)) * x) ∘
              (fun x => (⟨a, ha⟩ : (N ⊔ s.range : Subgroup G)) * x)) = id :=
          funext fun x => inv_mul_cancel_left (⟨a, ha⟩ : (N ⊔ s.range : Subgroup G)) x
        rw [e, Measure.map_id] }

  have hNT : N ≤ T := by
    intro n hn
    refine ⟨Subgroup.mem_sup_left hn, ?_⟩
    have e : (fun x : (N ⊔ s.range : Subgroup G) =>
        (⟨n, Subgroup.mem_sup_left hn⟩ : (N ⊔ s.range : Subgroup G)) * x) ∘ φ =
        φ ∘ Prod.map id (fun m : N => (⟨n, hn⟩ : N) * m) := by
      funext p
      apply Subtype.ext
      simp [φ, mul_assoc]
    rw [hm, Measure.map_map (measurable_const_mul _) hφ, e,
      ← Measure.map_map hφ (measurable_id.prodMap (measurable_const_mul _)),
      ← Measure.map_prod_map μ ν measurable_id (measurable_const_mul _), Measure.map_id,
      map_mul_left_eq_self]

  have hST : s.range ≤ T := by
    rintro _ ⟨h₀, rfl⟩
    refine ⟨Subgroup.mem_sup_right ⟨h₀, rfl⟩, ?_⟩
    let c : N → N := fun m => ⟨s h₀ * m.1 * (s h₀)⁻¹, hnorm m.1 m.2 h₀⟩
    have hcm : Measurable c :=
      (Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const)
        _).measurable
    have hcν : ν.map c = ν := by
      rw [← hemb.comap_map (ν.map c), Measure.map_map hemb.measurable hcm]
      have e : (Subtype.val ∘ c) = (fun m : N => s h₀ * m.1 * (s h₀)⁻¹) := rfl
      rw [e, hc h₀, hemb.comap_map]
    have e : (fun x : (N ⊔ s.range : Subgroup G) =>
        (⟨s h₀, Subgroup.mem_sup_right ⟨h₀, rfl⟩⟩ : (N ⊔ s.range : Subgroup G)) * x) ∘ φ =
        φ ∘ Prod.map (fun h => h₀ * h) c := by
      funext p
      apply Subtype.ext
      simp [φ, c, mul_assoc]
    rw [hm, Measure.map_map (measurable_const_mul _) hφ, e,
      ← Measure.map_map hφ ((measurable_const_mul _).prodMap hcm),
      ← Measure.map_prod_map μ ν (measurable_const_mul _) hcm, hcν, map_mul_left_eq_self]
  have hT : N ⊔ s.range ≤ T := sup_le hNT hST
  exact ⟨fun k => by
    obtain ⟨hk, ek⟩ := hT k.2
    exact ek⟩
