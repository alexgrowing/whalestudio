import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealPointsToUnitaryGroupVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceTensorRatFiniteAlgebraModuleTopology
open NumberField GlobalTheory.LKTrip GlobalTheory.HTBetti GlobalTheory.Kg IsDedekindDomain
open scoped TensorProduct Matrix.Norms.L2Operator RestrictedProduct

noncomputable section

open Topology

namespace GlobalTheory.GfTop

theorem td_of_inj {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TotallyDisconnectedSpace Y]
    {f : X → Y} (hf : Continuous f) (hi : Function.Injective f) : TotallyDisconnectedSpace X :=
  ⟨fun s _ hs => Set.subsingleton_of_image hi s
    (isTotallyDisconnected_of_totallyDisconnectedSpace (f '' s) (f '' s) subset_rfl (hs.image f hf.continuousOn))⟩

theorem props_of_closedEmb {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [LocallyCompactSpace Y]
    [T2Space Y] [TotallyDisconnectedSpace Y] [SecondCountableTopology Y] {f : X → Y} (hf : IsClosedEmbedding f) :
    LocallyCompactSpace X ∧ T2Space X ∧ TotallyDisconnectedSpace X ∧ SecondCountableTopology X :=
  ⟨hf.locallyCompactSpace, hf.isEmbedding.t2Space, td_of_inj hf.continuous hf.injective,
    hf.isEmbedding.secondCountableTopology⟩

theorem isClosedEmbedding_embedProduct' (A : Type*) [TopologicalSpace A] [Monoid A] [ContinuousMul A] [T2Space A] :
    IsClosedEmbedding (Units.embedProduct A) := by
  refine ⟨Units.isEmbedding_embedProduct, ?_⟩
  have h : Set.range (Units.embedProduct A) =
      {x : A × Aᵐᵒᵖ | x.1 * x.2.unop = 1 ∧ x.2.unop * x.1 = 1} := by
    ext ⟨a, b⟩
    constructor
    · rintro ⟨u, hu⟩
      rw [← hu]
      simp
    · rintro ⟨h1, h2⟩
      exact ⟨⟨a, b.unop, h1, h2⟩, rfl⟩
  rw [h]
  exact (isClosed_eq (continuous_fst.mul (MulOpposite.continuous_unop.comp continuous_snd)) continuous_const).inter
    (isClosed_eq ((MulOpposite.continuous_unop.comp continuous_snd).mul continuous_fst) continuous_const)

theorem units_props (A : Type*) [TopologicalSpace A] [Monoid A] [ContinuousMul A] [LocallyCompactSpace A]
    [T2Space A] [TotallyDisconnectedSpace A] [SecondCountableTopology A] :
    LocallyCompactSpace Aˣ ∧ T2Space Aˣ ∧ TotallyDisconnectedSpace Aˣ ∧ SecondCountableTopology Aˣ := by
  obtain ⟨o1, o2, o3, o4⟩ := props_of_closedEmb (MulOpposite.opHomeomorph (M := A)).symm.isClosedEmbedding
  exact props_of_closedEmb (isClosedEmbedding_embedProduct' A)

theorem module_props (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
    [T2Space R] [TotallyDisconnectedSpace R] [SecondCountableTopology R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] [TopologicalSpace M]
    [IsModuleTopology R M] :
    LocallyCompactSpace M ∧ T2Space M ∧ TotallyDisconnectedSpace M ∧ SecondCountableTopology M := by
  haveI : ContinuousAdd M := IsModuleTopology.toContinuousAdd R M
  let b := Module.Free.chooseBasis R M
  let e : M ≃ₜ (Module.Free.ChooseBasisIndex R M → R) :=
    { toEquiv := b.equivFun.toEquiv
      continuous_toFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap }
  exact props_of_closedEmb e.isClosedEmbedding

section UPts

open GlobalTheory.LKTrip

variable {C : Type} [Ring C] [Algebra ℚ C] [Module.Finite ℚ C] (star : C →+* Cᵐᵒᵖ)

theorem upts_props (R : Type) [CommRing R] [Algebra ℚ R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [T2Space R] [TotallyDisconnectedSpace R] [SecondCountableTopology R] :
    LocallyCompactSpace (UPts star R) ∧ T2Space (UPts star R) ∧ TotallyDisconnectedSpace (UPts star R) ∧
      SecondCountableTopology (UPts star R) := by
  letI : TopologicalSpace (R ⊗[ℚ] C) := moduleTopology R (R ⊗[ℚ] C)
  haveI : IsModuleTopology R (R ⊗[ℚ] C) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[ℚ] C) := IsModuleTopology.isTopologicalRing R (R ⊗[ℚ] C)
  obtain ⟨m1, m2, m3, m4⟩ := module_props R (R ⊗[ℚ] C)
  obtain ⟨u1, u2, u3, u4⟩ := units_props (R ⊗[ℚ] C)
  obtain ⟨v1, v2, v3, v4⟩ := units_props R
  let f : C →ₗ[ℚ] C := (MulOpposite.opLinearEquiv ℚ).symm.toLinearMap ∘ₗ star.toRatAlgHom.toLinearMap
  have hσeq : (fun y : R ⊗[ℚ] C => (starT star R y).unop) = LinearMap.baseChange R f := by
    funext y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r x =>
      rw [starT_tmul, LinearMap.baseChange_tmul]
      rfl
    | add x y hx hy => simp only [map_add, MulOpposite.unop_add] at hx hy ⊢; rw [hx, hy]
  have hσ : Continuous (fun y : R ⊗[ℚ] C => (starT star R y).unop) := by
    rw [hσeq]
    exact IsModuleTopology.continuous_of_linearMap _
  have hcl : IsClosed ((UPts star R : Subgroup ((R ⊗[ℚ] C)ˣ × Rˣ)) : Set ((R ⊗[ℚ] C)ˣ × Rˣ)) := by
    have hs : ((UPts star R : Subgroup ((R ⊗[ℚ] C)ˣ × Rˣ)) : Set ((R ⊗[ℚ] C)ˣ × Rˣ)) =
        {x | ((x.1 : (R ⊗[ℚ] C)ˣ) : R ⊗[ℚ] C) * (starT star R ((x.1 : (R ⊗[ℚ] C)ˣ) : R ⊗[ℚ] C)).unop =
          algebraMap R (R ⊗[ℚ] C) ((x.2 : Rˣ) : R)} := rfl
    rw [hs]
    exact isClosed_eq ((Units.continuous_val.comp continuous_fst).mul (hσ.comp (Units.continuous_val.comp continuous_fst)))
      ((continuous_algebraMap R (R ⊗[ℚ] C)).comp (Units.continuous_val.comp continuous_snd))
  exact props_of_closedEmb hcl.isClosedEmbedding_subtypeVal

end UPts

end GlobalTheory.GfTop

namespace GlobalTheory.GfTop

open GlobalTheory.LKTrip IsDedekindDomain

section AfP

variable (p : ℕ)

theorem t2Space_afP : T2Space (AfP p) :=
  inferInstanceAs (T2Space (Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]))

theorem finiteAdeleRingAway_locallyCompactSpace : LocallyCompactSpace (AfP p) :=
  (LevelExists.isCompact_intAfP p).locallyCompactSpace_of_mem_nhds_of_addGroup
    ((LevelExists.isOpen_intAfP p).mem_nhds (LevelExists.intAfP p).zero_mem)

theorem finiteAdeleRingAway_totallyDisconnectedSpace : TotallyDisconnectedSpace (AfP p) :=
  td_of_inj (X := Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ])
    (f := fun x => (x : ∀ v : AwayP p, v.1.adicCompletion ℚ)) RestrictedProduct.continuous_coe
    (fun x y h => RestrictedProduct.ext _ _ fun i => congrFun h i)

theorem countable_awayP : Countable (AwayP p) := by
  have hI : Countable (Ideal ℤ) := by
    have hs : Function.Surjective (fun n : ℤ => Ideal.span {n}) := fun I =>
      ⟨Submodule.IsPrincipal.generator I, Ideal.span_singleton_generator I⟩
    exact hs.countable
  have hi : Function.Injective (fun v : AwayP p => v.1.asIdeal) := fun v w h =>
    Subtype.ext (HeightOneSpectrum.ext h)
  exact hi.countable

theorem compl_sc (v : HeightOneSpectrum ℤ) : SecondCountableTopology (v.adicCompletion ℚ) := by
  haveI : Fact ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ).Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toHomeomorph.isEmbedding.secondCountableTopology

theorem finiteAdeleRingAway_secondCountableTopology : SecondCountableTopology (AfP p) := by
  haveI := countable_awayP p
  haveI : ∀ v : AwayP p, SecondCountableTopology (v.1.adicCompletion ℚ) := fun v => compl_sc v.1
  have hAopen : ∀ v : AwayP p, IsOpen ((v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ))) :=
    fun v => Valued.isOpen_valuationSubring _
  have hS : ∀ S : Finset (AwayP p), Filter.cofinite ≤ Filter.principal ((S : Set (AwayP p))ᶜ) := fun S =>
    Filter.le_principal_iff.2 S.finite_toSet.compl_mem_cofinite
  let U : Finset (AwayP p) → Set (Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]) :=
    fun S => Set.range (RestrictedProduct.inclusion (fun v : AwayP p => v.1.adicCompletion ℚ)
      (fun v : AwayP p => (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ))) (hS S))
  have hUo : ∀ S, IsOpen (U S) := fun S =>
    (RestrictedProduct.isOpenEmbedding_inclusion_principal hAopen (hS S)).isOpen_range
  have hsc : ∀ S, SecondCountableTopology (U S) := fun S => by
    haveI : SecondCountableTopology (Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]_[
        Filter.principal ((S : Set (AwayP p))ᶜ)]) :=
      RestrictedProduct.isEmbedding_coe_of_principal.secondCountableTopology
    exact (RestrictedProduct.isOpenEmbedding_inclusion_principal hAopen
      (hS S)).isEmbedding.toHomeomorph.symm.isEmbedding.secondCountableTopology
  have hcov : ⋃ S, U S = Set.univ := by
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨(Filter.eventually_cofinite.1 x.2).toFinset, ?_⟩
    show x ∈ Set.range _
    rw [RestrictedProduct.range_inclusion]
    refine Filter.eventually_principal.2 fun i hi => ?_
    by_contra h
    exact hi (by rw [Finset.mem_coe, Set.Finite.mem_toFinset]; exact h)
  exact @TopologicalSpace.secondCountableTopology_of_countable_cover _ _ _ _ U hsc hUo hcov

end AfP

open GlobalTheory.HTBetti

end GlobalTheory.GfTop
