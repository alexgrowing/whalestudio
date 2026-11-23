import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DecayNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsInfEqOne

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IdeleDecay

open scoped Classical

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem continuous_evI : Continuous (evI F) := by
  have h : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
    change Continuous fun x : InfiniteAdeleRing F =>
      ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
       (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
    refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
    · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
    · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)
  exact h.comp continuous_fst

def intAdeles : AddSubgroup (AF F) where
  carrier := {a | ∀ v, evFin F v a ∈ v.adicCompletionIntegers F}
  zero_mem' := fun v => by rw [map_zero]; exact zero_mem _
  add_mem' := fun ha hb v => by rw [map_add]; exact add_mem (ha v) (hb v)
  neg_mem' := fun ha v => by rw [map_neg]; exact neg_mem (ha v)

theorem isOpen_intAdeles : IsOpen (intAdeles F : Set (AF F)) :=
  (RestrictedProduct.isOpen_forall_mem fun v : HeightOneSpectrum (𝓞 F) =>
    Valued.isOpen_valuationSubring (v.adicCompletion F)).preimage continuous_snd

theorem isClopen_intAdeles : IsClopen (intAdeles F : Set (AF F)) :=
  ⟨AddSubgroup.isClosed_of_isOpen _ (isOpen_intAdeles F), isOpen_intAdeles F⟩

theorem continuous_coord : Continuous (coord F E) := by
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).equivFun.toLinearMap

theorem continuous_size : Continuous (size F E) := by
  unfold size
  exact continuous_finset_sum _ fun i _ =>
    ((continuous_evI F).comp ((continuous_apply i).comp (continuous_coord F E))).norm

theorem continuous_decay (N m : ℕ) : Continuous (decay F E N m) := by
  have hS : IsClopen {l : (AE F E)ˣ | ∀ i v, evFin F v ((m : AF F) * coord F E l.1 i) ∈ v.adicCompletionIntegers F} := by
    have : {l : (AE F E)ˣ | ∀ i v, evFin F v ((m : AF F) * coord F E l.1 i) ∈ v.adicCompletionIntegers F} =
        ⋂ i, (fun l : (AE F E)ˣ => (m : AF F) * coord F E l.1 i) ⁻¹' (intAdeles F : Set (AF F)) := by
      ext l; simp [intAdeles]
    rw [this]
    refine isClopen_iInter_of_finite fun i => (isClopen_intAdeles F).preimage ?_
    exact continuous_const.mul ((continuous_apply i).comp ((continuous_coord F E).comp Units.continuous_val))
  have hf : Continuous fun l : (AE F E)ˣ => ((1 + size F E l.1) ^ N)⁻¹ :=
    ((continuous_const.add ((continuous_size F E).comp Units.continuous_val)).pow N).inv₀ fun l =>
      pow_ne_zero _ (add_pos_of_pos_of_nonneg one_pos (size_nonneg _)).ne'
  unfold decay
  refine continuous_if ?_ hf.continuousOn continuous_const.continuousOn
  intro a ha
  rw [hS.frontier_eq] at ha
  exact absurd ha (Set.notMem_empty a)

theorem measurable_decay (N m : ℕ) : Measurable (decay F E N m) := by
  letI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  exact (continuous_decay F E N m).measurable

end GlobalTheory.IdeleDecay
