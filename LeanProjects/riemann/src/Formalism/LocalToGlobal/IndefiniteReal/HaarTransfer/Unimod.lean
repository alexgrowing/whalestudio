import Mathlib

namespace Formalism.IndefR.Leaf

open MeasureTheory

def HaarRightInvProd : Prop :=
  ∀ (G₁ G₂ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁]
    [T2Space G₁] [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁]
    [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂]
    [T2Space G₂] [SecondCountableTopology G₂] [MeasurableSpace G₂] [BorelSpace G₂],
    (∀ μ : Measure G₁, μ.IsHaarMeasure → μ.IsMulRightInvariant) →
    (∀ μ : Measure G₂, μ.IsHaarMeasure → μ.IsMulRightInvariant) →
      ∀ μ : Measure (G₁ × G₂), μ.IsHaarMeasure → μ.IsMulRightInvariant

def HaarRightInvPi : Prop :=
  ∀ (ι : Type) [Fintype ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, T2Space (G i)]
    [∀ i, SecondCountableTopology (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)],
    (∀ i, ∀ μ : Measure (G i), μ.IsHaarMeasure → μ.IsMulRightInvariant) →
      ∀ μ : Measure (∀ i, G i), μ.IsHaarMeasure → μ.IsMulRightInvariant

def HaarRightInvTransfer : Prop :=
  ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [MeasurableSpace H] [BorelSpace H] (_e : G ≃ₜ* H),
    (∀ μ : Measure G, μ.IsHaarMeasure → μ.IsMulRightInvariant) →
      ∀ ν : Measure H, ν.IsHaarMeasure → ν.IsMulRightInvariant

end Formalism.IndefR.Leaf
