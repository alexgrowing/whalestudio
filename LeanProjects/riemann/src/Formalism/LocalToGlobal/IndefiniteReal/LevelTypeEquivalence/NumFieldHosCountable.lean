import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.BaseSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicIntegersCompact.IsCompactAdicCompletionIntegers

open scoped TensorProduct ENNReal RestrictedProduct
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Topology Filter

noncomputable section

namespace Formalism.IndefR.Eqv.G5

section Count

variable (F : Type) [Field F] [NumberField F]

theorem numField_countable : Countable F := by
  exact Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)

theorem numField_hos_countable : Countable (HeightOneSpectrum (𝓞 F)) := by
  have := numField_countable F
  have : Countable (𝓞 F) := inferInstanceAs (Countable {x : F // x ∈ integralClosure ℤ F})
  have hs : Function.Surjective (fun s : Finset (𝓞 F) => Ideal.span (s : Set (𝓞 F))) := by
    intro I
    obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
    exact ⟨s, hs⟩
  have : Countable (Ideal (𝓞 F)) := hs.countable
  exact Function.Injective.countable (f := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
    (fun v w h => HeightOneSpectrum.ext h)

end Count

section Local

variable {F : Type} [Field F] [NumberField F]

theorem fv_secondCountable (v : HeightOneSpectrum (𝓞 F)) : SecondCountableTopology (Fv F v) := by
  have := numField_countable F
  have : TopologicalSpace.SeparableSpace (Fv F v) :=
    TopologicalSpace.SeparableSpace.of_denseRange _ (HeightOneSpectrum.denseRange_algebraMap F v)
  exact UniformSpace.secondCountable_of_separable (Fv F v)

theorem fv_locallyCompact (v : HeightOneSpectrum (𝓞 F)) : LocallyCompactSpace (Fv F v) := by
  have hc : IsCompact ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    PI.IntAdCpctOpenWork.isCompact_adicCompletionIntegers v
  have ho : IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    Valued.isOpen_valuationSubring _
  exact hc.locallyCompactSpace_of_mem_nhds_of_addGroup (ho.mem_nhds (zero_mem _))

theorem compl_secondCountable (w : InfinitePlace F) : SecondCountableTopology w.Completion := by
  have := numField_countable F
  have : Countable (WithAbs w.1) := Countable.of_equiv F (WithAbs.equiv w.1).symm
  have : TopologicalSpace.SeparableSpace w.Completion :=
    TopologicalSpace.SeparableSpace.of_denseRange _ (InfinitePlace.Completion.denseRange_coe w)
  exact UniformSpace.secondCountable_of_separable _

theorem ainf_secondCountable : SecondCountableTopology (Ainf F) := by
  have := fun w : InfinitePlace F => compl_secondCountable w
  exact inferInstanceAs (SecondCountableTopology ((w : InfinitePlace F) → w.Completion))

theorem t2Space_Ainf : T2Space (Ainf F) :=
  inferInstanceAs (T2Space ((w : InfinitePlace F) → w.Completion))

end Local

section Fin

variable {F : Type} [Field F] [NumberField F]

theorem af_locallyCompact : LocallyCompactSpace (Af F) := by
  have : ∀ v : HeightOneSpectrum (𝓞 F), LocallyCompactSpace (v.adicCompletion F) :=
    fun v => fv_locallyCompact v
  have : Fact (∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F)))) :=
    ⟨fun v => Valued.isOpen_valuationSubring _⟩
  exact inferInstanceAs (LocallyCompactSpace
    (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]))

theorem finite_adeles_t2 : T2Space (Af F) :=
  inferInstanceAs (T2Space
    (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]))

theorem af_secondCountable : SecondCountableTopology (Af F) := by
  have := numField_hos_countable F
  have hfv : ∀ v : HeightOneSpectrum (𝓞 F), SecondCountableTopology (v.adicCompletion F) :=
    fun v => fv_secondCountable v
  let R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F
  let A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  have hAo : ∀ v, IsOpen (A v) := fun v => Valued.isOpen_valuationSubring _
  have hS : ∀ T : Finset (HeightOneSpectrum (𝓞 F)), cofinite ≤ 𝓟 ((T : Set (HeightOneSpectrum (𝓞 F)))ᶜ) := by
    intro T
    rw [le_principal_iff, mem_cofinite, compl_compl]
    exact T.finite_toSet
  let U : Finset (HeightOneSpectrum (𝓞 F)) → Set (Πʳ v, [R v, A v]) :=
    fun T => Set.range (RestrictedProduct.inclusion R A (hS T))
  have hU : ∀ T, IsOpenEmbedding (RestrictedProduct.inclusion R A (hS T)) :=
    fun T => RestrictedProduct.isOpenEmbedding_inclusion_principal hAo (hS T)
  have hsc : ∀ T, SecondCountableTopology (U T) := by
    intro T
    have : SecondCountableTopology (Πʳ v, [R v, A v]_[𝓟 ((T : Set (HeightOneSpectrum (𝓞 F)))ᶜ)]) :=
      RestrictedProduct.isEmbedding_coe_of_principal.secondCountableTopology
    exact (hU T).isEmbedding.toHomeomorph.symm.secondCountableTopology
  have hcov : ⋃ T, U T = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    have hx : Set.Finite {v | x v ∉ A v} := x.2
    refine Set.mem_iUnion.2 ⟨hx.toFinset, ?_⟩
    show x ∈ Set.range (RestrictedProduct.inclusion R A (hS hx.toFinset))
    rw [RestrictedProduct.range_inclusion]
    refine eventually_principal.2 fun v hv => ?_
    by_contra h
    exact hv (by simpa using h)
  exact @TopologicalSpace.secondCountableTopology_of_countable_cover _ _ _ _ U hsc
    (fun T => (hU T).isOpen_range) hcov

end Fin

section Tens

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem tens_homeo (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    (hE : Module.finrank F E = 2) : Nonempty ((R ⊗[F] E) ≃ₜ (Fin 2 → R)) := by
  have : Module.Finite F E := Module.finite_of_finrank_eq_succ hE
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hE
  let L : (R ⊗[F] E) ≃ₗ[R] (Fin 2 → R) := (Algebra.TensorProduct.basis R b).equivFun
  have : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R (R ⊗[F] E)
  exact ⟨{ toEquiv := L.toEquiv
           continuous_toFun := IsModuleTopology.continuous_of_linearMap L.toLinearMap
           continuous_invFun := IsModuleTopology.continuous_of_linearMap L.symm.toLinearMap }⟩

theorem tens_ring (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    (hE : Module.finrank F E = 2) : IsTopologicalRing (R ⊗[F] E) := by
  have : Module.Finite F E := Module.finite_of_finrank_eq_succ hE
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hE
  have : Module.Finite R (R ⊗[F] E) := Module.Finite.of_basis (Algebra.TensorProduct.basis R b)
  have : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  exact IsModuleTopology.isTopologicalRing R (R ⊗[F] E)

theorem tens_facts (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] (hE : Module.finrank F E = 2) :
    IsTopologicalRing (R ⊗[F] E) ∧ T2Space (R ⊗[F] E) ∧ LocallyCompactSpace (R ⊗[F] E) ∧
      SecondCountableTopology (R ⊗[F] E) ∧ BorelSpace (R ⊗[F] E) := by
  obtain ⟨e⟩ := tens_homeo (E := E) R hE
  exact ⟨tens_ring R hE, e.isEmbedding.t2Space, e.isClosedEmbedding.locallyCompactSpace,
    e.isEmbedding.isInducing.secondCountableTopology, ⟨rfl⟩⟩

theorem sigR_continuous (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] (σ : E →ₐ[F] E) : Continuous (sigR R σ) := by
  have : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R (R ⊗[F] E)
  have h : (sigR R σ : R ⊗[F] E → R ⊗[F] E) = LinearMap.baseChange R σ.toLinearMap := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [sigR]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [h]
  exact IsModuleTopology.continuous_of_linearMap _

end Tens

section Grp

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem ha_facts (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] (hE : Module.finrank F E = 2)
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    IsTopologicalGroup (HA R σ J) ∧ T2Space (HA R σ J) ∧ LocallyCompactSpace (HA R σ J) ∧
      SecondCountableTopology (HA R σ J) ∧ BorelSpace (HA R σ J) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := tens_facts (E := E) R hE
  have : T2Space (Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin M → Fin M → R ⊗[F] E))
  have : LocallyCompactSpace (Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin M → Fin M → R ⊗[F] E))
  have : SecondCountableTopology (Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin M → Fin M → R ⊗[F] E))
  have : SecondCountableTopology (Matrix (Fin M) (Fin M) (R ⊗[F] E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.isInducing.secondCountableTopology
  have : SecondCountableTopology (GL (Fin M) (R ⊗[F] E)) :=
    Units.isEmbedding_embedProduct.isInducing.secondCountableTopology
  have hcl : IsClosed (HR R σ J : Set (GL (Fin M) (R ⊗[F] E))) := by
    have hv : Continuous (fun g : GL (Fin M) (R ⊗[F] E) => (g : Matrix (Fin M) (Fin M) (R ⊗[F] E))) :=
      Units.continuous_val
    have hc : Continuous (fun g : GL (Fin M) (R ⊗[F] E) =>
        Formalism.UG.cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J *
          (g : Matrix (Fin M) (Fin M) (R ⊗[F] E))) := by
      unfold Formalism.UG.cT
      exact (((hv.matrix_map (sigR_continuous R σ)).matrix_transpose).matrix_mul
        continuous_const).matrix_mul hv
    exact isClosed_eq hc continuous_const
  have hLC : LocallyCompactSpace (HR R σ J) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  exact ⟨inferInstanceAs (IsTopologicalGroup (HR R σ J)), inferInstanceAs (T2Space (HR R σ J)), hLC,
    (IsInducing.subtypeVal (t := (HR R σ J : Set (GL (Fin M) (R ⊗[F] E))))).secondCountableTopology, ⟨rfl⟩⟩

end Grp

theorem af_facts (F : Type) [Field F] [NumberField F] :
    T2Space (AF F) ∧ LocallyCompactSpace (AF F) ∧ SecondCountableTopology (AF F) := by
  have : T2Space (Ainf F) := t2Space_Ainf (F := F)
  have : SecondCountableTopology (Ainf F) := ainf_secondCountable (F := F)
  have : T2Space (Af F) := finite_adeles_t2 (F := F)
  have : LocallyCompactSpace (Af F) := af_locallyCompact (F := F)
  have : SecondCountableTopology (Af F) := af_secondCountable (F := F)
  exact ⟨inferInstanceAs (T2Space (Ainf F × Af F)), inferInstanceAs (LocallyCompactSpace (Ainf F × Af F)),
    inferInstanceAs (SecondCountableTopology (Ainf F × Af F))⟩

end Formalism.IndefR.Eqv.G5
