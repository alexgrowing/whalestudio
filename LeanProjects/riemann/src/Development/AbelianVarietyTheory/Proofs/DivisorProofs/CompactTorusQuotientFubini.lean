import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordMeasure
open MeasureTheory
open scoped NNReal ENNReal Pointwise

namespace GlobalTheory.ParabolicCoord

def coordSet {G T : Type} [Group G] [CommGroup T] (Q : Subgroup G) (m : T →* G) : Set G :=
  {x : G | ∃ q ∈ Q, ∃ t, x = q * m t}

def coordAct {G T : Type} [Group G] [CommGroup T] (Q : Subgroup G) (m : T →* G) :
    MulAction (Q × T) (coordSet Q m) where
  smul g x := ⟨(g.1 : G) * x * (m g.2)⁻¹, by
    obtain ⟨q, hq, t, ht⟩ := x.2
    refine ⟨g.1 * q, Q.mul_mem g.1.2 hq, t * g.2⁻¹, ?_⟩
    rw [ht, map_mul, map_inv]; group⟩
  one_smul x := Subtype.ext (by show ((1 : Q) : G) * x * (m 1)⁻¹ = x; simp)
  mul_smul g h x := Subtype.ext (by
    show ((g * h).1 : G) * x * (m (g * h).2)⁻¹ = (g.1 : G) * ((h.1 : G) * x * (m h.2)⁻¹) * (m g.2)⁻¹
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, map_mul]; group)

theorem isCompact_coord_preimage {G T : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [CommGroup T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T]
    [SecondCountableTopology T] [T2Space T]
    (Q : Subgroup G) (m : T →* G) (hQ : IsClosed (Q : Set G)) (hm : Continuous m)
    (hinj : ∀ t, m t ∈ Q → t = 1) (hP : IsClosed {x : G | ∃ q ∈ Q, ∃ t, x = q * m t})
    (D : Set G) (hD : IsCompact D) :
    IsCompact {p : T × Q | (p.2 : G) * (m p.1)⁻¹ ∈ D} := by
  let Pset := coordSet Q m
  change IsClosed (coordSet Q m) at hP
  haveI : SecondCountableTopology Q := TopologicalSpace.Subtype.secondCountableTopology (Q : Set G)
  haveI : LocallyCompactSpace Q := hQ.locallyCompactSpace
  haveI : SigmaCompactSpace Q := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaCompactSpace T := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : LocallyCompactSpace Pset := hP.locallyCompactSpace
  haveI : BaireSpace Pset := BaireSpace.of_t2Space_locallyCompactSpace
  letI := coordAct Q m
  haveI : ContinuousSMul (Q × T) Pset := by
    refine ⟨continuous_induced_rng.2 ?_⟩
    show Continuous fun z : (Q × T) × Pset => (z.1.1 : G) * (z.2 : G) * (m z.1.2)⁻¹
    fun_prop
  let o : Pset := ⟨1, 1, Q.one_mem, 1, by simp⟩
  have hact : ∀ g : Q × T, ((g • o : Pset) : G) = (g.1 : G) * (m g.2)⁻¹ := fun g => by
    show (g.1 : G) * 1 * (m g.2)⁻¹ = _; simp
  have hsurj : ∀ x : Pset, ∃ g : Q × T, g • o = x := by
    intro x
    obtain ⟨q, hq, t, ht⟩ := x.2
    exact ⟨(⟨q, hq⟩, t⁻¹), Subtype.ext (by rw [hact, ht]; simp)⟩
  haveI : MulAction.IsPretransitive (Q × T) Pset := ⟨fun x y => by
    obtain ⟨g, rfl⟩ := hsurj x
    obtain ⟨h, rfl⟩ := hsurj y
    exact ⟨h * g⁻¹, by rw [smul_smul, inv_mul_cancel_right]⟩⟩
  have hO : IsOpenMap fun g : Q × T => g • o := isOpenMap_smul_of_sigmaCompact o
  have hinj' : Function.Injective fun g : Q × T => g • o := by
    intro g h hgh
    have e : (g.1 : G) * (m g.2)⁻¹ = (h.1 : G) * (m h.2)⁻¹ := by
      rw [← hact, ← hact]; exact congrArg Subtype.val hgh
    have h2 : m (g.2 * h.2⁻¹) ∈ Q := by
      have : m (g.2 * h.2⁻¹) = ((h.1 : G))⁻¹ * g.1 := by
        rw [map_mul, map_inv]
        calc m g.2 * (m h.2)⁻¹ = (m h.2)⁻¹ * m g.2 := by
                rw [← map_inv, ← map_mul, ← map_mul, mul_comm]
          _ = _ := by
                have := congrArg (fun x => ((h.1 : G))⁻¹ * x * m g.2) e
                rw [show ((h.1 : G))⁻¹ * ((g.1 : G) * (m g.2)⁻¹) * m g.2 = ((h.1 : G))⁻¹ * g.1 by group,
                  show ((h.1 : G))⁻¹ * ((h.1 : G) * (m h.2)⁻¹) * m g.2 = (m h.2)⁻¹ * m g.2 by group]
                  at this
                exact this.symm
      rw [this]; exact Q.mul_mem (Q.inv_mem h.1.2) g.1.2
    have ht : g.2 = h.2 := by
      have := hinj _ h2; rwa [mul_inv_eq_one] at this
    have hq : g.1 = h.1 := by
      apply Subtype.ext; rw [ht] at e; simpa using e
    exact Prod.ext hq ht
  have hcont : Continuous fun g : Q × T => g • o := continuous_id.smul continuous_const
  let e : (Q × T) ≃ₜ Pset :=
    (Equiv.ofBijective _ ⟨hinj', fun x => hsurj x⟩).toHomeomorphOfContinuousOpen hcont hO
  have hemb : Topology.IsClosedEmbedding (Subtype.val : Pset → G) := hP.isClosedEmbedding_subtypeVal
  have h1 : IsCompact ((Subtype.val : Pset → G) ⁻¹' D) := hemb.isCompact_preimage hD
  have h2 : IsCompact (e ⁻¹' ((Subtype.val : Pset → G) ⁻¹' D)) := e.isCompact_preimage.2 h1
  have h3 := h2.image (continuous_swap)
  convert h3 using 1
  ext ⟨t, q⟩
  simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_preimage, Prod.exists, Prod.swap_prod_mk]
  constructor
  · intro h; exact ⟨q, t, by
      show ((e (q, t) : Pset) : G) ∈ D
      show (((q, t) : Q × T) • o : Pset).1 ∈ D
      rw [hact]; exact h, rfl⟩
  · rintro ⟨a, b, hab, hh⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hh
    have : (((a, b) : Q × T) • o : Pset).1 ∈ D := hab
    rwa [hact] at this

end GlobalTheory.ParabolicCoord

namespace GlobalTheory.ParabolicCoord

theorem coordMeasure_isFiniteMeasureOnCompacts :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [SecondCountableTopology K]
    [T2Space K] [MeasurableSpace K] [BorelSpace K]
    (T : Type) [CommGroup T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [SecondCountableTopology T]
    [T2Space T] [MeasurableSpace T] [BorelSpace T]
    (Q : Subgroup G) (κ : K →* G) (m : T →* G) (δ : T →* ℝ≥0) (μK : Measure K) (μT : Measure T) (μQ : Measure Q),
    IsClosed (Q : Set G) → Continuous κ → Topology.IsClosedEmbedding m → Continuous δ → μK.IsHaarMeasure → μT.IsHaarMeasure → μQ.IsHaarMeasure →
    ∀ hn : (∀ t, ∀ q ∈ Q, (m t)⁻¹ * q * m t ∈ Q),
    (∀ t, m t ∈ Q → t = 1) →
    IsClosed {x : G | ∃ q ∈ Q, ∃ t, x = q * m t} →
    (∀ x : G, ∃ q ∈ Q, ∃ t k, x = q * (m t)⁻¹ * κ k) →
    IsFiniteMeasureOnCompacts (GlobalTheory.ParabolicCoord.coordMeasure Q κ m δ μQ μT μK) := by
  intro G _ _ _ _ _ _ _ _ K _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ Q κ m δ μK μT μQ hQ hκ hm hδ _ _ _ _ hinj hP _
  haveI : IsLocallyFiniteMeasure (μT.withDensity fun t => ((δ t : ℝ≥0) : ℝ≥0∞)) :=
    IsLocallyFiniteMeasure.withDensity_coe (μ := μT) hδ
  constructor
  intro C hC
  unfold coordMeasure
  set f : K × (T × Q) → G := fun p => (p.2.2 : G) * (m p.2.1)⁻¹ * κ p.1
  set μ := μK.prod ((μT.withDensity fun t => ((δ t : ℝ≥0) : ℝ≥0∞)).prod μQ)
  by_cases hf : AEMeasurable f μ
  · rw [Measure.map_apply_of_aemeasurable hf hC.measurableSet]
    set D : Set G := C * (Set.range κ)⁻¹
    have hD : IsCompact D := hC.mul (isCompact_range hκ).inv
    have hA := isCompact_coord_preimage Q m hQ hm.continuous hinj hP D hD
    have hsub : f ⁻¹' C ⊆ Set.univ ×ˢ {p : T × Q | (p.2 : G) * (m p.1)⁻¹ ∈ D} := by
      intro p hp
      refine ⟨Set.mem_univ _, ?_⟩
      show (p.2.2 : G) * (m p.2.1)⁻¹ ∈ D
      have : (p.2.2 : G) * (m p.2.1)⁻¹ = f p * (κ p.1)⁻¹ := by simp [f]
      rw [this]
      exact Set.mul_mem_mul hp (Set.inv_mem_inv.2 ⟨p.1, rfl⟩)
    exact lt_of_le_of_lt (measure_mono hsub) ((isCompact_univ.prod hA).measure_lt_top)
  · rw [Measure.map_of_not_aemeasurable hf]; simp

end GlobalTheory.ParabolicCoord
