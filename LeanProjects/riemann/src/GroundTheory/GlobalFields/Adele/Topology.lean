import Mathlib
import GroundTheory.GlobalFields.LocalAtPlace
import GroundTheory.GlobalFields.Adele.Approximation
import GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
import GroundTheory.GlobalFields.IdeleGroups.Restricted

open NumberField IsDedekindDomain Topology Filter
open scoped NumberField.AdeleRing RestrictedProduct

namespace GroundTheory.Global

variable (K : Type*) [Field K] [NumberField K]

instance fact_isOpen_adicCompletionIntegers :
    Fact (∀ v : HeightOneSpectrum (𝓞 K),
      IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
  ⟨fun v ↦ isOpen_adicCompletionIntegers v⟩

instance locallyCompactSpace_finiteAdeleRing :
    LocallyCompactSpace (FiniteAdeleRing (𝓞 K) K) :=
  RestrictedProduct.locallyCompactSpace_of_addGroup
    (R := fun v : HeightOneSpectrum (𝓞 K) ↦ v.adicCompletion K)
    (B := fun v ↦ v.adicCompletionIntegers K)
    (.of_forall fun v ↦ isCompact_adicCompletionIntegers v)

theorem t2Space_finiteAdeleRing : T2Space (FiniteAdeleRing (𝓞 K) K) :=
  inferInstance

instance locallyCompactSpace_adeleRing : LocallyCompactSpace 𝔸[K] :=
  inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))

theorem t2Space_adeleRing : T2Space 𝔸[K] :=
  inferInstance

instance IdeleGroup.locallyCompactSpace : LocallyCompactSpace (IdeleGroup K) :=
  inferInstance

theorem IdeleGroup.t2Space : T2Space (IdeleGroup K) :=
  inferInstance

instance locallyCompactSpace_units_finiteAdeleRing :
    LocallyCompactSpace (FiniteAdeleRing (𝓞 K) K)ˣ :=
  inferInstance

instance locallyCompactSpace_units_infiniteAdeleRing :
    LocallyCompactSpace (InfiniteAdeleRing K)ˣ :=
  inferInstance

theorem isCompact_units_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 K)) :
    IsCompact ((Submonoid.ofClass (v.adicCompletionIntegers K)).units :
      Set (v.adicCompletion K)ˣ) := by
  have h : IsCompact ((v.adicCompletionIntegers K : Set (v.adicCompletion K)) ×ˢ
      (MulOpposite.unop ⁻¹' (v.adicCompletionIntegers K : Set (v.adicCompletion K)))) :=
    (isCompact_adicCompletionIntegers v).prod
      (MulOpposite.opHomeomorph.symm.isCompact_preimage.2 (isCompact_adicCompletionIntegers v))
  convert Units.isClosedEmbedding_embedProduct.isCompact_preimage h using 1
  ext u
  simp only [SetLike.mem_coe, Submonoid.mem_units_iff, Set.mem_preimage, Set.mem_prod,
    Units.embedProduct_apply, MulOpposite.unop_op]
  exact Iff.rfl

instance locallyCompactSpace_restrictedProduct_units :
    LocallyCompactSpace (Πʳ v : HeightOneSpectrum (𝓞 K),
      [(v.adicCompletion K)ˣ, (Submonoid.ofClass (v.adicCompletionIntegers K)).units]) :=
  haveI : Fact (∀ v : HeightOneSpectrum (𝓞 K),
      IsOpen ((Submonoid.ofClass (v.adicCompletionIntegers K)).units :
        Set (v.adicCompletion K)ˣ)) :=
    ⟨fun v ↦ IdeleGroup.isOpen_units_adicCompletionIntegers K v⟩
  RestrictedProduct.locallyCompactSpace_of_group
    (R := fun v : HeightOneSpectrum (𝓞 K) ↦ (v.adicCompletion K)ˣ)
    (B := fun v ↦ (Submonoid.ofClass (v.adicCompletionIntegers K)).units)
    (.of_forall fun v ↦ isCompact_units_adicCompletionIntegers K v)

end GroundTheory.Global
