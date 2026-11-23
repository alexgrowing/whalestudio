import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.UniqGen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensAll
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensFibV
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.GramMapFibreExistence

noncomputable section

namespace PI.OmFibreUniq.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology
open PI.OmFibreUniq PI.VolStabSW PI.VolStabSW.TensAllW
open scoped TensorProduct

theorem td_of_inj {α β : Type} [TopologicalSpace α] [TopologicalSpace β]
    [TotallyDisconnectedSpace α] (e : β → α) (he : Continuous e) (hi : Function.Injective e) :
    TotallyDisconnectedSpace β :=
  ⟨fun t _ ht x hx y hy =>
    hi ((isTotallyDisconnected_of_totallyDisconnectedSpace _ _ (Set.subset_univ _)
      (ht.image e he.continuousOn)) ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)⟩

theorem gram_map_fibre_uniqueness : FibUniq := by
  intro F E _ _ _ _ _ σ n J v a μ ν hν fib fib' h h'
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have := secondCountable_Fv F v
  have := locallyCompact_Fv F v
  obtain ⟨ι, _, ⟨e⟩⟩ := PI.AdicCompletionValuation.exists_homeomorph_tens (F := F) (E := E) (Fv F v)
  have : TotallyDisconnectedSpace (Fv F v ⊗[F] E) := td_of_inj e e.continuous e.injective
  have : LocallyCompactSpace (Fv F v ⊗[F] E) := e.isClosedEmbedding.locallyCompactSpace
  have : T2Space (Fv F v ⊗[F] E) := e.isEmbedding.t2Space
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR (Fv F v) σ a) := ⟨rfl⟩
  have : LocallyCompactSpace (HermR (Fv F v) σ a) :=
    (isClosed_HermR (Fv F v) σ a).isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Fv F v ⊗[F] E))
  have : SecondCountableTopology (HermR (Fv F v) σ a) :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  have := hν
  have hfree : IsOpen (IndepV (E := E) (n := n) v a) :=
    isOpen_linIndep (Module.finBasis F E) (Fv F v) (isOpen_units_Fv F v) (lip_field _)
      (a := a) (M := n)
  have hA : ∀ S : Set (HermR (Fv F v) σ a), MeasurableSet S →
      MeasurableSet (gramR (Fv F v) σ J ⁻¹' (Subtype.val '' S)) := by
    intro S hS
    letI : MeasurableSpace (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) := borel _
    haveI : BorelSpace (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) := ⟨rfl⟩
    have hcl : IsClosedEmbedding
        (Subtype.val : HermR (Fv F v) σ a → Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
      (isClosed_HermR (Fv F v) σ a).isClosedEmbedding_subtypeVal
    have hemb : MeasurableEmbedding
        (Subtype.val : HermR (Fv F v) σ a → Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
      hcl.measurableEmbedding
    exact (hemb.measurableSet_image.2 hS).preimage (continuous_gramR (Fv F v) σ J).measurable
  exact fib_unique μ ν (gramR (Fv F v) σ J) Subtype.val (IndepV (E := E) (n := n) v a) hA
    Subtype.val_injective hfree fib fib' h h'

theorem omUnique_of_sdEx (h0 : SdEx) {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (a : ℕ) : OmUnique σ J ψ v a :=
  omUnique_of σ J ψ v a h0 gram_map_fibre_existence gram_map_fibre_uniqueness

end PI.OmFibreUniq.W
