import Mathlib

open MeasureTheory MeasureTheory.Measure Topology
open scoped ENNReal NNReal

namespace GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre

def IsUnimodular (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] : Prop :=
  ∀ μ : Measure G, μ.IsHaarMeasure → μ.IsMulRightInvariant

section Defs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)

structure IsInvariantRadon [MeasurableSpace (G ⧸ H)] (μ : Measure (G ⧸ H)) : Prop where
  ne_zero : μ ≠ 0
  finiteOnCompacts : IsFiniteMeasureOnCompacts μ
  invariant : SMulInvariantMeasure G (G ⧸ H) μ

noncomputable def fibreIntegral (ν : Measure H) [ν.IsMulLeftInvariant] (f : G → ℝ≥0∞) :
    G ⧸ H → ℝ≥0∞ :=
  Quotient.lift (fun g : G => ∫⁻ h : H, f (g * h) ∂ν) (by
    intro a b hab
    have hab' : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.mp hab
    have := lintegral_mul_left_eq_self (μ := ν) (fun h : H => f (a * h)) ⟨a⁻¹ * b, hab'⟩
    simp only [Subgroup.coe_mul] at this
    rw [← this]
    simp [← mul_assoc])

@[simp] theorem fibreIntegral_mk (ν : Measure H) [ν.IsMulLeftInvariant] (f : G → ℝ≥0∞) (g : G) :
    fibreIntegral H ν f (g : G ⧸ H) = ∫⁻ h : H, f (g * h) ∂ν := rfl

def QuotientFormula [MeasurableSpace (G ⧸ H)] (dg : Measure G) (ν : Measure H)
    [ν.IsMulLeftInvariant] (μ : Measure (G ⧸ H)) : Prop :=
  ∀ f : G → ℝ≥0∞, Measurable f →
    Measurable (fibreIntegral H ν f) ∧ ∫⁻ g, f g ∂dg = ∫⁻ q, fibreIntegral H ν f q ∂μ

abbrev RightCosets : Type := Quotient (QuotientGroup.rightRel H)

def rightCoset (g : G) : RightCosets H := Quotient.mk (QuotientGroup.rightRel H) g

def invCoset : G ⧸ H → RightCosets H :=
  (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm

open MeasureTheory MeasureTheory.Measure Topology in
open scoped ENNReal NNReal in
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) in
omit [MeasurableSpace G] [BorelSpace G] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.continuous_invCoset : Continuous (_root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.invCoset H) := by
  refine continuous_quot_lift _ ?_
  exact continuous_quot_mk.comp continuous_inv

noncomputable def rightMeasure [MeasurableSpace (G ⧸ H)] [MeasurableSpace (RightCosets H)]
    (μ : Measure (G ⧸ H)) : Measure (RightCosets H) :=
  μ.map (invCoset H)

open MeasureTheory MeasureTheory.Measure Topology in
open scoped ENNReal NNReal in
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) in
omit [MeasurableSpace G] [BorelSpace G] in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.IsInvariantRadon.regular [LocallyCompactSpace G]
    [SecondCountableTopology G] [IsClosed (H : Set G)] [MeasurableSpace (G ⧸ H)]
    [BorelSpace (G ⧸ H)] {μ : Measure (G ⧸ H)} (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.IsInvariantRadon H μ) :
    μ.Regular := by
  haveI := h.finiteOnCompacts
  infer_instance

def ExistsUniqueInvariantRadon [MeasurableSpace (G ⧸ H)] : Prop :=
  (∃ μ : Measure (G ⧸ H), IsInvariantRadon H μ) ∧
    ∀ μ μ' : Measure (G ⧸ H), IsInvariantRadon H μ → IsInvariantRadon H μ' →
      ∃ c : ℝ≥0, 0 < c ∧ μ' = c • μ

end Defs

def InvariantMeasureClause : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)],
    IsClosed (H : Set G) → IsUnimodular G → IsUnimodular H → ExistsUniqueInvariantRadon H

def NormaliseQuotientClause : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)],
    IsClosed (H : Set G) → IsUnimodular G → IsUnimodular H →
    ∀ (dg : Measure G) [dg.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure],
      ∃! μ : Measure (G ⧸ H), IsInvariantRadon H μ ∧ QuotientFormula H dg ν μ

def NormaliseSubgroupClause : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)],
    IsClosed (H : Set G) → IsUnimodular G → IsUnimodular H →
    ∀ (dg : Measure G) [dg.IsHaarMeasure] (μ : Measure (G ⧸ H)), IsInvariantRadon H μ →
      ∃! ν : Measure H, ∃ _ : ν.IsHaarMeasure, QuotientFormula H dg ν μ

def NormaliseGroupClause : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)],
    IsClosed (H : Set G) → IsUnimodular G → IsUnimodular H →
    ∀ (ν : Measure H) [ν.IsHaarMeasure] (μ : Measure (G ⧸ H)), IsInvariantRadon H μ →
      ∃! dg : Measure G, dg.IsHaarMeasure ∧ QuotientFormula H dg ν μ

def DiscreteClause : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)]
    [MeasurableSpace (RightCosets H)] [BorelSpace (RightCosets H)],
    IsClosed (H : Set G) → IsUnimodular G → IsUnimodular H →
    ∀ (dg : Measure G) [dg.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure]
      (μ : Measure (G ⧸ H)), IsInvariantRadon H μ → QuotientFormula H dg ν μ →
    ∀ (Γ : Subgroup G), Γ ≤ H → DiscreteTopology Γ →
      (∃ D : Set G, MeasurableSet D ∧ IsFundamentalDomain Γ D dg) ∧
      (∃ D' : Set H, MeasurableSet D' ∧ IsFundamentalDomain (Γ.subgroupOf H) D' ν) ∧
      ∀ (D : Set G) (D' : Set H), IsFundamentalDomain Γ D dg →
        IsFundamentalDomain (Γ.subgroupOf H) D' ν →
        ∀ f : G → ℝ≥0∞, Measurable f → (∀ γ ∈ Γ, ∀ g : G, f (γ * g) = f g) →
          ∃ Φ : RightCosets H → ℝ≥0∞, Measurable Φ ∧
            (∀ g : G, Φ (rightCoset H g) = ∫⁻ h in D', f ((h : G) * g) ∂ν) ∧
            ∫⁻ g in D, f g ∂dg = ∫⁻ q, Φ q ∂(rightMeasure H μ)

def ModulusClause : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G]
    (H : Subgroup G) [LocallyCompactSpace H] [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)],
    IsClosed (H : Set G) →
    (∀ h : H, modularCharacter (G := G) (h : G) = modularCharacter (G := H) h) →
    ExistsUniqueInvariantRadon H

def CompactClause : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G]
    (H : Subgroup G) [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)],
    IsCompact (H : Set G) → ExistsUniqueInvariantRadon H

def QuotientMeasures : Prop :=
  InvariantMeasureClause ∧ NormaliseQuotientClause ∧ NormaliseSubgroupClause ∧
    NormaliseGroupClause ∧ DiscreteClause ∧ ModulusClause ∧ CompactClause

example {G : Type} [Group G] (Γ : Subgroup G) (γ : Γ) (g : G) : γ • g = (γ : G) * g := rfl

example {G : Type} [Group G] (H : Subgroup G) (a g : G) :
    a • (g : G ⧸ H) = ((a * g : G) : G ⧸ H) := rfl

example (G : Type) [CommGroup G] [TopologicalSpace G] [MeasurableSpace G] : IsUnimodular G := by
  intro μ hμ
  refine ⟨fun g => ?_⟩
  have := map_mul_left_eq_self μ g
  simpa [mul_comm] using this

example (G : Type) [Group G] [Finite G] [TopologicalSpace G] (H : Subgroup G)
    [MeasurableSpace (G ⧸ H)] [DiscreteMeasurableSpace (G ⧸ H)] :
    IsInvariantRadon H (Measure.count : Measure (G ⧸ H)) where
  ne_zero := Measure.count_ne_zero''
  finiteOnCompacts := inferInstance
  invariant := ⟨fun c s _ => by
    have h1 := Measure.count_injective_image (f := (MulAction.toPerm c).symm)
      (MulAction.toPerm c : (G ⧸ H) ≃ (G ⧸ H)).symm.injective s
    rw [← h1]
    congr 1
    exact (Equiv.image_symm_eq_preimage (MulAction.toPerm c) s).symm⟩

end GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
