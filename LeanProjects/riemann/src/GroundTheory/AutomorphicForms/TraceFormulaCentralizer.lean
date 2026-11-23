import Mathlib
import GroundTheory.AutomorphicForms.TraceFormulaGeometric

open MeasureTheory Topology Filter Set Function
open scoped ENNReal Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace RightCosetSpace

section Maps

variable {G : Type*} [Group G]

def mapOfLe {H₁ H₂ : Subgroup G} (h : H₁ ≤ H₂) : RightCosetSpace H₁ → RightCosetSpace H₂ :=
  Quotient.map' id (by
    rintro a b ⟨η, rfl⟩
    exact ⟨⟨η, h η.2⟩, rfl⟩)

@[simp] theorem mapOfLe_mk {H₁ H₂ : Subgroup G} (h : H₁ ≤ H₂) (x : G) :
    mapOfLe h (mk H₁ x) = mk H₂ x :=
  rfl

theorem measurable_mapOfLe [MeasurableSpace G] {H₁ H₂ : Subgroup G} (h : H₁ ≤ H₂) :
    Measurable (mapOfLe h) :=
  measurable_from_quotient.2 measurable_quotient_mk''

def centralizerLattice (Γ : Subgroup G) (γ : G) : Subgroup (Subgroup.centralizer {γ}) :=
  Γ.comap (Subgroup.centralizer {γ}).subtype

theorem mem_centralizerLattice {Γ : Subgroup G} {γ : G} {h : Subgroup.centralizer {γ}} :
    h ∈ centralizerLattice Γ γ ↔ (h : G) ∈ Γ :=
  Iff.rfl

end Maps

section Topology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

theorem isClosed_centralizer (γ : G) : IsClosed (Subgroup.centralizer {γ} : Set G) :=
  Set.isClosed_centralizer {γ}

instance locallyCompactSpace_centralizer [LocallyCompactSpace G] (γ : G) :
    LocallyCompactSpace (Subgroup.centralizer {γ}) :=
  (isClosed_centralizer γ).locallyCompactSpace

instance discreteTopology_centralizerLattice (Γ : Subgroup G) [DiscreteTopology Γ] (γ : G) :
    DiscreteTopology (centralizerLattice Γ γ) :=
  DiscreteTopology.of_continuous_injective
    (f := fun h : centralizerLattice Γ γ => (⟨((h : Subgroup.centralizer {γ}) : G), h.2⟩ : Γ))
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    (fun a b hab => by
      simp only at hab
      exact Subtype.ext (Subtype.ext (by injection hab)))

instance secondCountableTopology_centralizer [SecondCountableTopology G] (γ : G) :
    SecondCountableTopology (Subgroup.centralizer {γ}) :=
  inferInstanceAs (SecondCountableTopology (Subgroup.centralizer {γ} : Set G))

variable [LocallyCompactSpace G] (Γ : Subgroup G) [DiscreteTopology Γ]

theorem compactSpace_centralizerLattice [CompactSpace (RightCosetSpace Γ)] (γ : Γ) :
    CompactSpace (RightCosetSpace (centralizerLattice Γ (γ : G))) := by
  classical
  obtain ⟨C, hC, hCcov⟩ := exists_isCompact_subset_mk_image (Γ := Γ) isCompact_univ
  set K₀ : Set G := (fun c => c * γ * c⁻¹) '' C with hK₀
  have hK₀c : IsCompact K₀ := hC.image (by fun_prop)
  have hT : {t : Γ | (t : G) ∈ K₀}.Finite := finite_setOf_mem_of_isCompact Γ hK₀c
  let dd : Γ → Γ := fun t =>
    if h : ∃ d : Γ, d⁻¹ * γ * d = t then h.choose else 1
  have hdd : ∀ t : Γ, (∃ d : Γ, d⁻¹ * γ * d = t) → (dd t)⁻¹ * γ * dd t = t := by
    intro t h
    simp only [dd, dif_pos h]
    exact h.choose_spec
  set K : Set G := ⋃ t ∈ {t : Γ | (t : G) ∈ K₀}, ((dd t : Γ) : G) • C with hK
  have hKc : IsCompact K := hT.isCompact_biUnion fun t _ => hC.smul _
  set K' : Set (Subgroup.centralizer {(γ : G)}) := Subtype.val ⁻¹' K
  have hK'c : IsCompact K' :=
    (isClosed_centralizer (γ : G)).isClosedEmbedding_subtypeVal.isCompact_preimage hKc
  refine ⟨?_⟩
  have hcov : mk (centralizerLattice Γ (γ : G)) '' K' = univ := by
    refine eq_univ_of_forall fun y => ?_
    obtain ⟨h, rfl⟩ := mk_surjective _ y
    obtain ⟨c, hcC, hc⟩ := hCcov (mem_univ (mk Γ (h : G)))
    obtain ⟨η, hη⟩ := mk_eq_mk_iff.1 hc

    change (η : G) * h = c at hη
    have hhγ : (h : G)⁻¹ * γ * h = γ := mem_centralizer_singleton_iff.1 h.2
    set t : Γ := η * γ * η⁻¹ with ht
    have htK : (t : G) ∈ K₀ := by
      refine ⟨c, hcC, ?_⟩
      rw [ht, ← hη]
      push_cast
      calc (η : G) * h * γ * ((η : G) * h)⁻¹
          = (η : G) * ((h : G) * γ * (h : G)⁻¹) * (η : G)⁻¹ := by group
        _ = (η : G) * γ * (η : G)⁻¹ := by
          congr 2
          calc (h : G) * γ * (h : G)⁻¹ = (h : G) * ((h : G)⁻¹ * γ * h) * (h : G)⁻¹ := by
                rw [hhγ]
            _ = γ := by group
    have hd := hdd t ⟨η⁻¹, by rw [ht, inv_inv]⟩
    set d := dd t

    have hdG : ((d : G))⁻¹ * γ * d = (η : G) * γ * (η : G)⁻¹ := by
      have := congrArg Subtype.val hd
      push_cast at this
      rw [this, ht]
      push_cast
      rfl
    have hεZ : ((η : G)⁻¹ * (d : G)⁻¹) ∈ Subgroup.centralizer {(γ : G)} := by
      rw [mem_centralizer_singleton_iff]
      calc ((η : G)⁻¹ * (d : G)⁻¹)⁻¹ * γ * ((η : G)⁻¹ * (d : G)⁻¹)
          = (d : G) * (((d : G))⁻¹ * γ * d) * (d : G)⁻¹ := by
            rw [hdG]; group
        _ = γ := by group
    set ε : Subgroup.centralizer {(γ : G)} := ⟨_, hεZ⟩
    have hεΓ : ε ∈ centralizerLattice Γ (γ : G) := by
      rw [mem_centralizerLattice]
      exact Γ.mul_mem (Γ.inv_mem η.2) (Γ.inv_mem d.2)
    refine ⟨(⟨ε, hεΓ⟩ : centralizerLattice Γ (γ : G))⁻¹ • h, ?_, ?_⟩
    ·
      change (ε : G)⁻¹ * h ∈ K
      rw [hK]
      refine mem_iUnion₂.2 ⟨t, htK, ?_⟩
      rw [mem_smul_set_iff']
      convert hcC using 1
      rw [← hη]
      change (d : G)⁻¹ * (((η : G)⁻¹ * (d : G)⁻¹)⁻¹ * h) = (η : G) * h
      group
    · exact mk_smul _ _
  rw [← hcov]
  exact hK'c.image (continuous_mk _)

end Topology

section Weil

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]

def IsWeilMeasure (H : Subgroup G) (μ : Measure G) (ν : Measure H)
    (ρ : Measure (RightCosetSpace H)) : Prop :=
  ∀ (φ : G → ℝ≥0∞) (F : RightCosetSpace H → ℝ≥0∞), Measurable φ →
    (∀ x, F (mk H x) = ∫⁻ h, φ ((h : G) * x) ∂ν) → ∫⁻ x, φ x ∂μ = ∫⁻ y, F y ∂ρ

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G]
  [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ]

omit [LocallyCompactSpace G] [T2Space G] in

theorem isFundamentalDomain_centralizerLattice (γ : G) (ν : Measure (Subgroup.centralizer {γ}))
    (x : G) : IsFundamentalDomain (centralizerLattice Γ γ)
      {h : Subgroup.centralizer {γ} | (h : G) * x ∈ fundamentalDomain (centralizerIn Γ γ)} ν := by
  refine IsFundamentalDomain.mk' ((measurableSet_fundamentalDomain _).preimage
    ((continuous_subtype_val.mul continuous_const).measurable)).nullMeasurableSet fun h => ?_
  obtain ⟨η, hη, hηu⟩ := existsUnique_smul_mem_fundamentalDomain (centralizerIn Γ γ) ((h : G) * x)
  have hηZ : (η : G) ∈ Subgroup.centralizer {γ} := centralizerIn_le_centralizer Γ γ η.2
  have hηΓ : (⟨η, hηZ⟩ : Subgroup.centralizer {γ}) ∈ centralizerLattice Γ γ :=
    centralizerIn_le Γ γ η.2
  refine ⟨⟨⟨η, hηZ⟩, hηΓ⟩, ?_, ?_⟩
  · change (η : G) * (h : G) * x ∈ fundamentalDomain (centralizerIn Γ γ)
    rw [mul_assoc]
    exact hη
  · rintro ⟨⟨l, hlZ⟩, hlΓ⟩ hl
    change l * (h : G) * x ∈ fundamentalDomain (centralizerIn Γ γ) at hl
    have hlC : l ∈ centralizerIn Γ γ := Subgroup.mem_inf.2 ⟨hlΓ, hlZ⟩
    have := hηu ⟨l, hlC⟩ (by
      change l * ((h : G) * x) ∈ fundamentalDomain (centralizerIn Γ γ)
      rw [← mul_assoc]; exact hl)
    have hl' : l = η := congrArg Subtype.val this
    subst hl'
    rfl

variable (μ : Measure G)

theorem smul_eq_map_of_isWeilMeasure [μ.IsMulLeftInvariant] (γ : G)
    (ν : Measure (Subgroup.centralizer {γ})) [ν.IsMulLeftInvariant]
    {ρ : Measure (RightCosetSpace (Subgroup.centralizer {γ}))}
    (hρ : IsWeilMeasure (Subgroup.centralizer {γ}) μ ν ρ) :
    quotientMeasure (centralizerLattice Γ γ) ν univ • ρ =
      Measure.map (mapOfLe (centralizerIn_le_centralizer Γ γ))
        (quotientMeasure (centralizerIn Γ γ) μ) := by
  set E := fundamentalDomain (centralizerIn Γ γ)
  set vol := quotientMeasure (centralizerLattice Γ γ) ν univ
  ext A hA
  have hmk : Measurable (mk (Subgroup.centralizer {γ})) := measurable_quotient_mk''
  have hEm : MeasurableSet E := measurableSet_fundamentalDomain _
  rw [Measure.smul_apply, Measure.map_apply (measurable_mapOfLe _) hA,
    quotientMeasure_apply μ (isFundamentalDomain_fundamentalDomain _ μ)
      (measurable_mapOfLe _ hA), smul_eq_mul]
  have hS : ∀ x : G, ν {h : Subgroup.centralizer {γ} | (h : G) * x ∈ E} = vol := fun x =>
    (quotientMeasure_univ ν (isFundamentalDomain_centralizerLattice Γ γ ν x)).symm
  have hw := hρ ((mk (Subgroup.centralizer {γ}) ⁻¹' A ∩ E).indicator 1) (A.indicator fun _ => vol)
    (measurable_one.indicator ((hmk hA).inter hEm)) (fun x => ?_)
  · rw [lintegral_indicator_one ((hmk hA).inter hEm), lintegral_indicator_const hA] at hw
    rw [← hw]
    rfl
  · have hind : (fun h : Subgroup.centralizer {γ} =>
        (mk (Subgroup.centralizer {γ}) ⁻¹' A ∩ E).indicator (1 : G → ℝ≥0∞) ((h : G) * x)) =
        fun h => (A.indicator fun _ => (1 : ℝ≥0∞)) (mk _ x) *
          {h : Subgroup.centralizer {γ} | (h : G) * x ∈ E}.indicator
            (1 : Subgroup.centralizer {γ} → ℝ≥0∞) h := by
      funext h
      have hmkh : mk (Subgroup.centralizer {γ}) ((h : G) * x) = mk _ x := mk_smul h x
      by_cases hx : mk (Subgroup.centralizer {γ}) x ∈ A
      · by_cases hE : (h : G) * x ∈ E
        · simp [indicator, hx, hE, hmkh]
        · simp [indicator, hx, hE]
      · simp [indicator, hx, hmkh]
    have hSm : MeasurableSet {h : Subgroup.centralizer {γ} | (h : G) * x ∈ E} :=
      hEm.preimage (continuous_subtype_val.mul continuous_const).measurable
    rw [hind, lintegral_const_mul _ (measurable_one.indicator hSm), lintegral_indicator_one hSm,
      hS x]
    by_cases hx : mk (Subgroup.centralizer {γ}) x ∈ A
    · simp [indicator, hx]
    · simp [indicator, hx]

theorem integral_conjOrbitFun_eq_smul [μ.IsMulLeftInvariant] (γ : G)
    (ν : Measure (Subgroup.centralizer {γ})) [ν.IsMulLeftInvariant]
    {ρ : Measure (RightCosetSpace (Subgroup.centralizer {γ}))}
    (hρ : IsWeilMeasure (Subgroup.centralizer {γ}) μ ν ρ)
    (f : CompactlySupportedContinuousMap G ℂ) :
    ∫ x, conjOrbitFun (centralizerIn Γ γ) (centralizerIn_le_centralizer Γ γ) f x
        ∂quotientMeasure (centralizerIn Γ γ) μ =
      (quotientMeasure (centralizerLattice Γ γ) ν univ).toReal •
        ∫ y, conjOrbitFun (Subgroup.centralizer {γ}) le_rfl f y ∂ρ := by
  have hmeas : Measurable (conjOrbitFun (Subgroup.centralizer {γ}) le_rfl f) :=
    measurable_from_quotient.2 (f.continuous.comp (by fun_prop)).measurable
  rw [← integral_smul_measure, smul_eq_map_of_isWeilMeasure Γ μ γ ν hρ,
    integral_map (measurable_mapOfLe _).aemeasurable hmeas.aestronglyMeasurable]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  obtain ⟨x, rfl⟩ := mk_surjective _ y
  rfl

end Weil

end RightCosetSpace

end

end GroundTheory.Automorphic
