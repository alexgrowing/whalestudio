import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsNhdsZeroPrincipalEqZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompactAdelesRationalPointsFiniteEventuallyZero

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic.FieldCocompact

theorem discrete_cocompact : ∀ (F : Type) [Field F] [NumberField F],
    (∃ C : Set (AdeleRing (𝓞 F) F), IsCompact C ∧
      ∀ y, ∃ l : F, y - algebraMap F (AdeleRing (𝓞 F) F) l ∈ C) ∧
    (∀ C : Set (AdeleRing (𝓞 F) F), IsCompact C →
      {l : F | algebraMap F (AdeleRing (𝓞 F) F) l ∈ C}.Finite) ∧
    NoncompactSpace (AdeleRing (𝓞 F) F) := by
  intro F _ _
  have hfin : ∀ C : Set (AdeleRing (𝓞 F) F), IsCompact C →
      {l : F | algebraMap F (AdeleRing (𝓞 F) F) l ∈ C}.Finite := fun C hC =>
    GlobalTheory.Eis.Conv.Discr.finite_of_isCompact (algebraMap F (AdeleRing (𝓞 F) F))
      (GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F) hC
  refine ⟨GlobalTheory.AdeleCocompact.exists_compact_adele F, hfin, ⟨fun h => ?_⟩⟩
  have h1 := hfin Set.univ h
  simp only [Set.mem_univ, Set.setOf_true] at h1
  exact Set.infinite_univ h1

end GlobalTheory.CompanionTheory.Adelic.FieldCocompact
