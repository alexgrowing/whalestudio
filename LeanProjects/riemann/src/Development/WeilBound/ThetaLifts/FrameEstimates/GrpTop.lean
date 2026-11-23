import Mathlib
import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteTopologyRationalUnitary
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem countable_numberField' (K : Type) [Field K] [NumberField K] : Countable K :=
  (Module.finBasis ℚ K).equivFun.injective.countable

private theorem countable_heightOneSpectrum_ringOfIntegers (K : Type) [Field K] [NumberField K] :
    Countable (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) := by
  have := countable_numberField' K
  have : Countable (NumberField.RingOfIntegers K) :=
    Function.Injective.countable (NumberField.RingOfIntegers.coe_injective (K := K))
  have hI : Countable (Ideal (NumberField.RingOfIntegers K)) := by
    refine Function.Surjective.countable
      (f := fun s : Finset (NumberField.RingOfIntegers K) => Ideal.span (s : Set (NumberField.RingOfIntegers K))) ?_
    intro I
    obtain ⟨s, hs⟩ := IsNoetherian.noetherian I
    exact ⟨s, hs⟩
  exact Function.Injective.countable
    (f := fun v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) => v.asIdeal)
    (fun v w h => IsDedekindDomain.HeightOneSpectrum.ext h)

private theorem univ_le_preimage_inf_of_univ_le (K : Type) [Field K] [NumberField K] :
    T2Space (NumberField.InfiniteAdeleRing K) ∧ SecondCountableTopology (NumberField.InfiniteAdeleRing K) := by
  have h : ∀ v : NumberField.InfinitePlace K, SecondCountableTopology v.Completion := fun v =>
    (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  exact ⟨inferInstanceAs (T2Space ((v : NumberField.InfinitePlace K) → v.Completion)),
    inferInstanceAs (SecondCountableTopology ((v : NumberField.InfinitePlace K) → v.Completion))⟩

private theorem fin_lemma_4 (K : Type) [Field K] [NumberField K] :
    T2Space (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers K) K) ∧
      SecondCountableTopology (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers K) K) := by
  have := countable_numberField' K
  have := countable_heightOneSpectrum_ringOfIntegers K
  have hsep : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      SecondCountableTopology (v.adicCompletion K) := by
    intro v
    have : TopologicalSpace.SeparableSpace (v.adicCompletion K) :=
      ⟨⟨_, Set.countable_range _, IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap K v⟩⟩
    exact UniformSpace.secondCountable_of_separable _
  have hopen : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      IsOpen ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) := fun v =>
    Valued.isOpen_valuationSubring _
  unfold IsDedekindDomain.FiniteAdeleRing
  constructor
  · exact T2Space.of_injective_continuous DFunLike.coe_injective RestrictedProduct.continuous_coe
  · have hS : ∀ s : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        (Filter.cofinite : Filter (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) ≤
          Filter.principal ((s : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))ᶜ) :=
      fun s => Filter.le_principal_iff.mpr s.finite_toSet.compl_mem_cofinite
    have hemb : ∀ s : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        Topology.IsOpenEmbedding (RestrictedProduct.inclusion (fun v => v.adicCompletion K)
          (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) (hS s)) := fun s =>
      RestrictedProduct.isOpenEmbedding_inclusion_principal hopen (hS s)
    have hsc : ∀ s : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        SecondCountableTopology (Set.range (RestrictedProduct.inclusion (fun v => v.adicCompletion K)
          (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) (hS s))) := by
      intro s
      have : SecondCountableTopology (RestrictedProduct (fun v => v.adicCompletion K)
          (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
          (Filter.principal ((s : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))ᶜ))) :=
        RestrictedProduct.isEmbedding_coe_of_principal.secondCountableTopology
      exact (hemb s).isEmbedding.toHomeomorph.symm.secondCountableTopology
    refine @TopologicalSpace.secondCountableTopology_of_countable_cover _ _ _ _ _ hsc (fun s => (hemb s).isOpen_range) ?_
    refine Set.eq_univ_of_forall fun x => ?_
    have hx := Filter.eventually_cofinite.mp x.2
    refine Set.mem_iUnion.mpr ⟨hx.toFinset, ⟨x.1, ?_⟩, rfl⟩
    exact Filter.eventually_principal.mpr fun v hv => by simpa using hv

private theorem AF_t2_secondCountable (K : Type) [Field K] [NumberField K] :
    T2Space (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF K) ∧ SecondCountableTopology (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF K) := by
  obtain ⟨h1, h2⟩ := univ_le_preimage_inf_of_univ_le K
  obtain ⟨h3, h4⟩ := fin_lemma_4 K
  exact ⟨inferInstanceAs (T2Space (NumberField.InfiniteAdeleRing K ×
      IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers K) K)),
    inferInstanceAs (SecondCountableTopology (NumberField.InfiniteAdeleRing K ×
      IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers K) K))⟩

private theorem AE_t2_secondCountable_locallyCompact (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    T2Space (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE K L) ∧ SecondCountableTopology (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE K L) ∧
      LocallyCompactSpace (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE K L) := by
  obtain ⟨h1, h2⟩ := AF_t2_secondCountable K
  have := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.modTop (F := K) (E := L)
  have : Nontrivial (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF K) := inferInstanceAs (Nontrivial (NumberField.InfiniteAdeleRing K ×
      IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers K) K))
  have : ContinuousAdd (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE K L) :=
    IsModuleTopology.toContinuousAdd (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF K) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE K L)
  let b := Module.finBasis (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF K) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE K L)
  have hc : Continuous b.equivFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
  have hc' : Continuous b.equivFun.symm := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap
  let h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE K L ≃ₜ (Fin _ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF K) :=
    { toEquiv := b.equivFun.toEquiv, continuous_toFun := hc, continuous_invFun := hc' }
  exact ⟨h.isEmbedding.t2Space, h.isEmbedding.secondCountableTopology, h.isClosedEmbedding.locallyCompactSpace⟩

private theorem GL_t2_secondCountable_locallyCompact (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    [SecondCountableTopology R] [LocallyCompactSpace R] (n : ℕ) :
    T2Space (GL (Fin n) R) ∧ SecondCountableTopology (GL (Fin n) R) ∧ LocallyCompactSpace (GL (Fin n) R) := by
  have : T2Space (Matrix (Fin n) (Fin n) R) := inferInstanceAs (T2Space (Fin n → Fin n → R))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) R) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → R))
  let ι : GL (Fin n) R → Matrix (Fin n) (Fin n) R × Matrix (Fin n) (Fin n) R := fun g => (↑g, ↑g⁻¹)
  have he : Topology.IsEmbedding ι := by
    exact ((Homeomorph.refl _).prodCongr MulOpposite.opHomeomorph.symm).isEmbedding.comp Units.isEmbedding_embedProduct
  have hr : Set.range ι = {p | p.1 * p.2 = 1 ∧ p.2 * p.1 = 1} := by
    ext p
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g.mul_inv, g.inv_mul⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨p.1, p.2, h1, h2⟩, rfl⟩
  have hcl : IsClosed (Set.range ι) := by
    rw [hr]
    exact (isClosed_eq (continuous_fst.mul continuous_snd) continuous_const).inter
      (isClosed_eq (continuous_snd.mul continuous_fst) continuous_const)
  have hce : Topology.IsClosedEmbedding ι := ⟨he, hcl⟩
  exact ⟨he.t2Space, he.secondCountableTopology, hce.locallyCompactSpace⟩

theorem lcsc_UA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    LocallyCompactSpace (UA σ J) ∧ SecondCountableTopology (UA σ J) ∧ T2Space (UA σ J) := by
  obtain ⟨h1, h2⟩ := AF_t2_secondCountable F
  have := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.modTop (F := F) (E := E)
  have : IsTopologicalRing (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) :=
    IsModuleTopology.isTopologicalRing (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)
  obtain ⟨a1, a2, a3⟩ := AE_t2_secondCountable_locallyCompact F E
  obtain ⟨g1, g2, g3⟩ := GL_t2_secondCountable_locallyCompact (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) n
  have : T2Space (Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) :=
    inferInstanceAs (T2Space (Fin n → Fin n → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E))
  have hc : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) :=
    IsModuleTopology.continuous_of_linearMap (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ).toLinearMap
  have hcl : IsClosed (GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J) :
      Set (GL (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E))) :=
    isClosed_eq (((Units.continuous_val.matrix_transpose).matrix_mul continuous_const).matrix_mul
      (Units.continuous_val.matrix_map hc)) continuous_const
  have hlc := hcl.locallyCompactSpace
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA
  exact ⟨hlc, Topology.IsEmbedding.subtypeVal.secondCountableTopology, inferInstance⟩

theorem continuous_ht (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    Continuous (ht : UA σ J → ℝ≥0) := by
  exact (GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val

theorem grpTop_of : GrpTop := by
  unfold GrpTop
  intro F E _ _ _ _ _ σ _ n J _
  have hE : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have hM : Countable (Matrix (Fin n) (Fin n) E) := by
    unfold Matrix
    infer_instance
  have hG : Countable (GL (Fin n) E) :=
    Function.Injective.countable (f := (Units.val : GL (Fin n) E → Matrix (Fin n) (Fin n) E)) (fun a b hab => Units.ext hab)
  let f := Matrix.GeneralLinearGroup.map (n := Fin n)
    (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F))
  have hR : Countable (Set.range f) := (Set.countable_range f).to_subtype
  refine ⟨(lcsc_UA σ J).1, (lcsc_UA σ J).2.1, (lcsc_UA σ J).2.2, ?_,
    GlobalTheory.RatUDiscrete.discreteTopology_ratU F E σ n J,
    Units.continuous_val.comp continuous_subtype_val, ?_, ?_⟩
  · have key : ∀ x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU σ J,
        ((x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ J) : GL (Fin n) _) ∈ Set.range f :=
      fun x => MonoidHom.mem_range.mp x.2
    refine Function.Injective.countable
      (f := fun x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU σ J => (⟨_, key x⟩ : Set.range f)) ?_
    intro x y h
    have h0 := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h0)
  · intro g h
    rfl
  · intro Ω hΩ
    obtain ⟨C, hC⟩ := (hΩ.image (continuous_ht σ J)).bddAbove
    exact ⟨C, fun g hg => hC ⟨g, hg, rfl⟩⟩

end PositivityTheory.ThKEst

end
