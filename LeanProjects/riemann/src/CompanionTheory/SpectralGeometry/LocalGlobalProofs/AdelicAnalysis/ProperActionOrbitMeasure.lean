import Mathlib
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotMeasUniq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.LintegralMulRightOfMem

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.AbsUniq

def stabilizerOf {G V : Type} [Group G] (act : G → V → V) (h1 : ∀ x, act 1 x = x)
    (hm : ∀ g h x, act (g * h) x = act g (act h x)) (x₀ : V) : Subgroup G where
  carrier := {g | act g x₀ = x₀}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [hm, hb, ha]
  one_mem' := h1 x₀
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    have h : act a⁻¹ (act a x₀) = x₀ := by rw [← hm, inv_mul_cancel, h1]
    rwa [ha] at h

def orbitQuot {G V : Type} [Group G] (act : G → V → V) (h1 : ∀ x, act 1 x = x)
    (hm : ∀ g h x, act (g * h) x = act g (act h x)) (x₀ : V) :
    G ⧸ stabilizerOf act h1 hm x₀ → V :=
  Quotient.lift (fun g => act g x₀) (by
    intro a b hab
    have h : a⁻¹ * b ∈ stabilizerOf act h1 hm x₀ := QuotientGroup.leftRel_apply.1 hab
    have h' : act (a⁻¹ * b) x₀ = x₀ := h
    show act a x₀ = act b x₀
    conv_lhs => rw [← h']
    rw [← hm, mul_inv_cancel_left])

theorem orbitQuot_mk {G V : Type} [Group G] (act : G → V → V) (h1 : ∀ x, act 1 x = x)
    (hm : ∀ g h x, act (g * h) x = act g (act h x)) (x₀ : V) (g : G) :
    orbitQuot act h1 hm x₀ (g : G ⧸ stabilizerOf act h1 hm x₀) = act g x₀ := rfl

theorem orbitQuot_injective {G V : Type} [Group G] (act : G → V → V) (h1 : ∀ x, act 1 x = x)
    (hm : ∀ g h x, act (g * h) x = act g (act h x)) (x₀ : V) :
    Function.Injective (orbitQuot act h1 hm x₀) := by
  intro a b
  induction a using QuotientGroup.induction_on with | _ a => ?_
  induction b using QuotientGroup.induction_on with | _ b => ?_
  intro hab
  rw [orbitQuot_mk, orbitQuot_mk] at hab
  refine QuotientGroup.eq.2 ?_
  show act (a⁻¹ * b) x₀ = x₀
  rw [hm, ← hab, ← hm, inv_mul_cancel, h1]

theorem orbitQuot_smul {G V : Type} [Group G] (act : G → V → V) (h1 : ∀ x, act 1 x = x)
    (hm : ∀ g h x, act (g * h) x = act g (act h x)) (x₀ : V) (g : G)
    (y : G ⧸ stabilizerOf act h1 hm x₀) :
    orbitQuot act h1 hm x₀ (g • y) = act g (orbitQuot act h1 hm x₀ y) := by
  induction y using QuotientGroup.induction_on with | _ a => ?_
  show act (g * a) x₀ = act g (act a x₀)
  rw [hm]

theorem range_orbitQuot {G V : Type} [Group G] (act : G → V → V) (h1 : ∀ x, act 1 x = x)
    (hm : ∀ g h x, act (g * h) x = act g (act h x)) (x₀ : V) (Z : Set V) (hx : x₀ ∈ Z)
    (hinv : ∀ g, ∀ x ∈ Z, act g x ∈ Z) (htr : ∀ x ∈ Z, ∀ y ∈ Z, ∃ g, act g x = y) :
    Set.range (orbitQuot act h1 hm x₀) = Z := by
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    induction a using QuotientGroup.induction_on with | _ a => ?_
    exact hinv a x₀ hx
  · intro hy
    obtain ⟨g, rfl⟩ := htr x₀ hx y hy
    exact ⟨(g : G ⧸ stabilizerOf act h1 hm x₀), rfl⟩

theorem continuous_orbitQuot {G V : Type} [Group G] [TopologicalSpace G]
    [TopologicalSpace V] (act : G → V → V) (hc : Continuous fun p : G × V => act p.1 p.2)
    (h1 : ∀ x, act 1 x = x)
    (hm : ∀ g h x, act (g * h) x = act g (act h x)) (x₀ : V) :
    Continuous (orbitQuot act h1 hm x₀) :=
  Continuous.quotient_lift (hc.comp (continuous_id.prodMk continuous_const)) _

theorem measurableEmbedding_orbitQuot {G V : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    [TopologicalSpace V] [T2Space V] [SecondCountableTopology V] [MeasurableSpace V]
    [BorelSpace V] (act : G → V → V) (hc : Continuous fun p : G × V => act p.1 p.2)
    (h1 : ∀ x, act 1 x = x)
    (hm : ∀ g h x, act (g * h) x = act g (act h x)) (x₀ : V) (Z : Set V) (hZ : IsClosed Z)
    (hx : x₀ ∈ Z) (hinv : ∀ g, ∀ x ∈ Z, act g x ∈ Z)
    (htr : ∀ x ∈ Z, ∀ y ∈ Z, ∃ g, act g x = y) :
    MeasurableEmbedding (orbitQuot act h1 hm x₀) := by
  have hcont : Continuous fun g : G => act g x₀ :=
    hc.comp (continuous_id.prodMk continuous_const)
  refine ⟨orbitQuot_injective act h1 hm x₀, ?_, ?_⟩
  · intro A hA
    rw [measurableSet_quotient]
    exact hcont.measurable hA
  · intro S hS
    have hS' : MeasurableSet ((fun g : G => (g : G ⧸ stabilizerOf act h1 hm x₀)) ⁻¹' S) :=
      measurableSet_quotient.1 hS
    let o : G → Z := fun g => ⟨act g x₀, hinv g x₀ hx⟩
    have hoc : Continuous o := hcont.subtype_mk _
    have hos : Function.Surjective o := by
      rintro ⟨y, hy⟩
      obtain ⟨g, rfl⟩ := htr x₀ hx y hy
      exact ⟨g, rfl⟩
    haveI : PolishSpace G := PI.AprimeInfA.polish_of_lcsc G
    have hb := hoc.map_eq_borel hos
    let T : Set Z := Subtype.val ⁻¹' (orbitQuot act h1 hm x₀ '' S)
    have hT : MeasurableSet T := by
      have hpre : o ⁻¹' T = (fun g : G => (g : G ⧸ stabilizerOf act h1 hm x₀)) ⁻¹' S := by
        ext g
        constructor
        · rintro ⟨y, hy, hyg⟩
          have : y = (g : G ⧸ stabilizerOf act h1 hm x₀) :=
            orbitQuot_injective act h1 hm x₀ hyg
          simpa [this] using hy
        · intro hg
          exact ⟨_, hg, rfl⟩
      have hm' : MeasurableSet[MeasurableSpace.map o ‹MeasurableSpace G›] T := by
        show MeasurableSet (o ⁻¹' T)
        rw [hpre]
        exact hS'
      rw [hb, ← BorelSpace.measurable_eq] at hm'
      exact hm'
    have himg : orbitQuot act h1 hm x₀ '' S = Subtype.val '' T := by
      rw [Subtype.image_preimage_coe, Set.inter_eq_right.2]
      rintro _ ⟨y, -, rfl⟩
      rw [← range_orbitQuot act h1 hm x₀ Z hx hinv htr]
      exact ⟨y, rfl⟩
    rw [himg]
    exact (MeasurableEmbedding.subtype_coe hZ.measurableSet).measurableSet_image.2 hT

theorem comap_orbitQuot_invariant {G V : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    [TopologicalSpace V] [T2Space V] [SecondCountableTopology V] [MeasurableSpace V]
    [BorelSpace V] (act : G → V → V) (hc : Continuous fun p : G × V => act p.1 p.2)
    (h1 : ∀ x, act 1 x = x)
    (hm : ∀ g h x, act (g * h) x = act g (act h x)) (x₀ : V)
    (hφ : MeasurableEmbedding (orbitQuot act h1 hm x₀)) (μ : Measure V)
    (hμ : ∀ g, μ.map (act g) = μ) (g : G) (s : Set (G ⧸ stabilizerOf act h1 hm x₀))
    (hs : MeasurableSet s) :
    μ.comap (orbitQuot act h1 hm x₀) ((fun y => g • y) ⁻¹' s) =
      μ.comap (orbitQuot act h1 hm x₀) s := by
  have hact : Measurable (act g) :=
    (hc.comp (continuous_const.prodMk continuous_id)).measurable
  rw [hφ.comap_apply, hφ.comap_apply]
  have himg : orbitQuot act h1 hm x₀ '' ((fun y => g • y) ⁻¹' s) =
      act g ⁻¹' (orbitQuot act h1 hm x₀ '' s) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨g • y, hy, orbitQuot_smul act h1 hm x₀ g y⟩
    · rintro ⟨y, hy, hyx⟩
      refine ⟨g⁻¹ • y, ?_, ?_⟩
      · show g • g⁻¹ • y ∈ s
        simpa using hy
      · rw [orbitQuot_smul, hyx, ← hm, inv_mul_cancel, h1]
  rw [himg]
  conv_rhs => rw [← hμ g]
  rw [Measure.map_apply hact (hφ.measurableSet_image.2 hs)]

theorem invariant_measure_unique :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
      [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
      (V : Type) [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V]
      [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (act : G → V → V),
      (Continuous fun p : G × V => act p.1 p.2) → (∀ x, act 1 x = x) →
      (∀ g h x, act (g * h) x = act g (act h x)) → ∀ Z : Set V, IsClosed Z →
      (∀ g, ∀ x ∈ Z, act g x ∈ Z) → (∀ x ∈ Z, ∀ y ∈ Z, ∃ g, act g x = y) →
      ∀ (μ ν : Measure V), IsLocallyFiniteMeasure μ → IsLocallyFiniteMeasure ν → μ Zᶜ = 0 →
      ν Zᶜ = 0 → (∀ g, μ.map (act g) = μ) → (∀ g, ν.map (act g) = ν) → ν ≠ 0 →
      ∃ c : ℝ≥0, μ = c • ν := by
  intro G _ _ _ _ _ _ _ _ V _ _ _ _ _ _ act hc h1 hm Z hZ hinv htr μ ν hμf hνf hμZ hνZ hμ hν hν0

  have hne : Z.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    apply hν0
    rw [← Measure.measure_univ_eq_zero]
    simpa [hemp] using hνZ
  obtain ⟨x₀, hx⟩ := hne
  set H := stabilizerOf act h1 hm x₀ with hH
  have hcont : Continuous fun g : G => act g x₀ :=
    hc.comp (continuous_id.prodMk continuous_const)
  have hHc : IsClosed (H : Set G) := by
    have : (H : Set G) = (fun g : G => act g x₀) ⁻¹' {x₀} := rfl
    rw [this]
    exact isClosed_singleton.preimage hcont
  set φ := orbitQuot act h1 hm x₀ with hφdef
  have hφc : Continuous φ := continuous_orbitQuot act hc h1 hm x₀
  have hφ : MeasurableEmbedding φ :=
    measurableEmbedding_orbitQuot act hc h1 hm x₀ Z hZ hx hinv htr
  have hr : Set.range φ = Z := range_orbitQuot act h1 hm x₀ Z hx hinv htr
  have hfin : ∀ (m : Measure V), IsLocallyFiniteMeasure m → ∀ K : Set (G ⧸ H), IsCompact K →
      m.comap φ K < ⊤ := by
    intro m _ K hK
    rw [hφ.comap_apply]
    exact (hK.image hφc).measure_lt_top
  have hrec : ∀ (m : Measure V), m Zᶜ = 0 → (m.comap φ).map φ = m := by
    intro m hm0
    rw [hφ.map_comap, hr]
    exact Measure.restrict_eq_self_of_ae_mem (by
      rw [ae_iff]; exact hm0)
  have hρ0 : ν.comap φ ≠ 0 := by
    intro h0
    apply hν0
    rw [← hrec ν hνZ, h0, Measure.map_zero]
  obtain ⟨c, hcc⟩ := PI.wqUnique G H hHc (ν.comap φ) (μ.comap φ) hρ0 (hfin ν hνf)
    (comap_orbitQuot_invariant act hc h1 hm x₀ hφ ν hν) (hfin μ hμf)
    (comap_orbitQuot_invariant act hc h1 hm x₀ hφ μ hμ)
  have hμν : μ = c • ν := by
    rw [← hrec μ hμZ, hcc, Measure.map_smul, hrec ν hνZ]

  have hct : c ≠ ⊤ := by
    rintro rfl
    have hK : ∃ K : Set V, IsCompact K ∧ ν K ≠ 0 := by
      by_contra hno
      push_neg at hno
      apply hν0
      rw [← Measure.measure_univ_eq_zero, ← iUnion_compactCovering V]
      exact measure_iUnion_null fun n => hno _ (isCompact_compactCovering V n)
    obtain ⟨K, hKc, hK0⟩ := hK
    have h := hKc.measure_lt_top (μ := μ)
    rw [hμν, Measure.smul_apply, smul_eq_mul, ENNReal.top_mul hK0] at h
    exact lt_irrefl _ h
  refine ⟨c.toNNReal, ?_⟩
  rw [hμν]
  ext s hs
  simp [Measure.smul_apply, ENNReal.smul_def, ENNReal.coe_toNNReal hct]

end GlobalTheory.CompanionTheory.SW.AbsUniq
