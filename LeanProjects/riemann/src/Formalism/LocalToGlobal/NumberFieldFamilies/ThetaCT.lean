import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCI
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegerSubgroupIntersection.IsOpenIntSub
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegerSubgroupIntersection.Imports
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegerSubgroupIntersection.IntInterAlt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Count

variable (F : Type) [Field F] [NumberField F]

theorem countable_F : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable

theorem countable_primes : Countable (HeightOneSpectrum (𝓞 F)) := by
  have := countable_F F
  have : Countable (𝓞 F) := Subtype.countable
  have h : Function.Surjective fun s : Finset (𝓞 F) => Ideal.span (s : Set (𝓞 F)) := fun I =>
    (IsNoetherian.noetherian I)
  have := h.countable
  exact Function.Injective.countable (f := HeightOneSpectrum.asIdeal) fun _ _ e => HeightOneSpectrum.ext e

theorem sc_Fv (v : HeightOneSpectrum (𝓞 F)) : SecondCountableTopology (v.adicCompletion F) := by
  have := countable_F F
  have : TopologicalSpace.SeparableSpace (v.adicCompletion F) :=
    ⟨_, Set.countable_range _, v.denseRange_algebraMap F⟩
  infer_instance

theorem sc_Af : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := by
  have := countable_primes F
  have := sc_Fv F
  have ho : ∀ v : HeightOneSpectrum (𝓞 F), IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    fun v => Valued.isOpen_valuationSubring _
  have hS : ∀ T : Finset (HeightOneSpectrum (𝓞 F)), Filter.cofinite ≤ Filter.principal ((T : Set (HeightOneSpectrum (𝓞 F)))ᶜ) := fun T =>
    Filter.le_principal_iff.2 T.finite_toSet.compl_mem_cofinite
  have he := fun T : Finset (HeightOneSpectrum (𝓞 F)) => RestrictedProduct.isOpenEmbedding_inclusion_principal ho (hS T)
  have hU : ∀ T : Finset (HeightOneSpectrum (𝓞 F)), SecondCountableTopology (Set.range (RestrictedProduct.inclusion
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set _)) (hS T))) :=
    fun T => by
      have := (RestrictedProduct.isEmbedding_coe_of_principal (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
        (A := fun v => (v.adicCompletionIntegers F : Set _)) (S := (T : Set (HeightOneSpectrum (𝓞 F)))ᶜ)).secondCountableTopology
      exact (he T).isEmbedding.toHomeomorph.symm.secondCountableTopology
  refine @TopologicalSpace.secondCountableTopology_of_countable_cover _ _ _ _ _ hU (fun T => (he T).isOpen_range) ?_
  refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
  have hx := Filter.eventually_cofinite.1 x.2
  refine ⟨hx.toFinset, ⟨x.1, Filter.eventually_principal.2 fun v hv => ?_⟩, rfl⟩
  by_contra h
  exact hv (by simpa using h)

variable {F} {E : Type} [Field E] [NumberField E] [Algebra F E]

end Count

variable {D : D7}

end Formalism.L2.Fam.ThC

end
