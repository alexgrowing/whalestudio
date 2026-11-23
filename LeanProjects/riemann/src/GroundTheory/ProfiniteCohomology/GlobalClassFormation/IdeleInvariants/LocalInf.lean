import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleInvariants.BrauerInvZOfIsSepClosureIdelesLocalResIdelesResF
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain IdeleLimit
  GroundTheory.Global.SemiLocal

open scoped NumberField.LiesOver

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K E : FiniteSubfield} [Fact (K ≤ E)]

set_option maxHeartbeats 4000000 in

theorem quadraticInv_infIdelesLocalRes_idelesResField_of_finrank_eq_one {v : InfinitePlace K.1}
    (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion)
    (ιE : ℚ̄ →ₐ[E.1] AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion)
    (y : cohomology (limitRep K) 2)
    (h1 : Module.finrank v.Completion (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion = 1) :
    quadraticInv (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion
        (AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion)
        (infAlgClosure_finrank_le_two _) (infAlgClosure_mul_mem_range_norm _)
        ((infIdelesLocalRes ιE 2).hom ((idelesResField K E 2).hom y)) =
      quadraticInv v.Completion (AlgebraicClosure v.Completion) (infAlgClosure_finrank_le_two v)
        (infAlgClosure_mul_mem_range_norm v) ((infIdelesLocalRes ι 2).hom y) := by
  have : (infPlaceOfEmbedding ι E : InfinitePlace E.1).LiesOver v := (infPlaceOfEmbedding ι E).2
  let c := infCompletionEmbedding ι E
  let L := c.fieldRange
  let : Algebra (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion (AlgebraicClosure v.Completion) :=
    c.toRingHom.toAlgebra
  have : IsScalarTower v.Completion (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion
      (AlgebraicClosure v.Completion) :=
    IsScalarTower.of_algebraMap_eq fun a => (c.commutes a).symm
  have : Algebra.IsAlgebraic (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion (AlgebraicClosure v.Completion) :=
    Algebra.IsAlgebraic.tower_top (K := v.Completion) _
  have : IsAlgClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion (AlgebraicClosure v.Completion) :=
    ⟨inferInstance, inferInstance⟩
  let θ : AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion ≃ₐ[(infPlaceOfEmbedding ι E :
      InfinitePlace E.1).Completion] AlgebraicClosure v.Completion := IsAlgClosure.equiv _ _ _
  let : Algebra E.1 (AlgebraicClosure v.Completion) :=
    ((algebraMap (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion (AlgebraicClosure v.Completion)).comp
      (algebraMap E.1 (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion)).toAlgebra
  have : IsScalarTower E.1 (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion (AlgebraicClosure v.Completion) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ιE' : ℚ̄ →ₐ[E.1] AlgebraicClosure v.Completion :=
    { ι.toRingHom with commutes' := fun t => (infCompletionEmbedding_algebraMap ι E t).symm }
  let ιE0 : ℚ̄ →ₐ[E.1] AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion :=
    (θ.symm.toAlgHom.restrictScalars E.1).comp ιE'
  have hι : ∀ t, θ.toRingEquiv (ιE0 t) = ι t := fun t => θ.apply_symm_apply (ι t)
  have hL : ∀ l ∈ L, ∃ t : (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion,
      θ.toRingEquiv (algebraMap _ (AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion) t) = l := by
    intro l hl
    obtain ⟨t, rfl⟩ := (AlgHom.mem_fieldRange).1 hl
    exact ⟨t, θ.commutes t⟩
  have : Algebra.IsIntegral L (AlgebraicClosure v.Completion) := Algebra.IsIntegral.tower_top v.Completion
  have hproj : ∀ z : IdeleLimit, θ.toRingEquiv (infIdelesProj ιE0 z : AlgebraicClosure _) =
      (infIdelesProj ι z : AlgebraicClosure v.Completion) :=
    infIdelesProj_eq_of_algebraMap (infPlaceOfEmbedding ι E) ι ιE0 θ.toRingEquiv hι fun a => by
      change θ (algebraMap _ (AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion)
        (algebraMap v.Completion _ a)) = _
      rw [θ.commutes]
      exact c.commutes a
  have key := cohomologyMapAlong_globalDecomp_idelesResField v.Completion
    (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion L θ.toRingEquiv hL ι ιE0 hι (infIdelesLocalMor ι)
    (infIdelesLocalMor ιE0) hproj 2 y

  let φ := (AlgEquiv.restrictScalarsHom v.Completion).comp (fieldConjHom v.Completion L θ.toRingEquiv hL)
  have hφ : Continuous φ := (continuous_restrictScalarsHom_of_tower v.Completion L (AlgebraicClosure v.Completion)).comp
    (continuous_fieldConjHom v.Completion L θ.toRingEquiv hL)
  let fφ : Rep.res φ (galUnitsZ v.Completion (AlgebraicClosure v.Completion)) ⟶
      galUnitsZ (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion
        (AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion) := (Rep.resFunctor (fieldConjHom v.Completion L θ.toRingEquiv hL)).map
    (unitsScalarsMor v.Completion (AlgebraicClosure v.Completion) L) ≫ fieldConjUnitsMor v.Completion L θ.toRingEquiv hL
  have key' : (infIdelesLocalRes ιE0 2).hom ((idelesResField K E 2).hom y) =
      (cohomologyMapAlong φ hφ fφ 2).hom ((infIdelesLocalRes ι 2).hom y) := by
    refine key.trans ?_
    rw [unitsScalarsRes, cohomologyMapAlong_comp]
    rfl
  rw [infIdelesLocalRes_eq_of_algHom ιE0 ιE, key']

  have hbot := Subalgebra.bot_eq_top_of_finrank_eq_one h1
  have hfix : ∀ (σ : Gal(AlgebraicClosure v.Completion / v.Completion))
      (t : (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion),
      θ.symm (σ (θ (algebraMap _ (AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion) t))) =
        algebraMap _ _ t := by
    intro σ t
    have ht : t ∈ (⊥ : Subalgebra v.Completion (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion) := by
      rw [hbot]
      trivial
    obtain ⟨k, rfl⟩ := Algebra.mem_bot.1 ht
    have hk : θ (algebraMap _ (AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion)
        (algebraMap v.Completion (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion k)) =
          algebraMap v.Completion (AlgebraicClosure v.Completion) k := by
      rw [θ.commutes]
      exact c.commutes k
    rw [hk, σ.commutes, ← hk, AlgEquiv.symm_apply_apply]
  let ψ : Gal(AlgebraicClosure v.Completion / v.Completion) →*
      Gal(AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion /
        (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion) :=
    { toFun := fun σ => AlgEquiv.ofRingEquiv (f := (θ.toRingEquiv.trans σ.toRingEquiv).trans θ.toRingEquiv.symm)
        (hfix σ)
      map_one' := AlgEquiv.ext fun x => θ.symm_apply_apply x
      map_mul' := fun σ τ => AlgEquiv.ext fun x => by
        change θ.symm (σ (τ (θ x))) = θ.symm (σ (θ (θ.symm (τ (θ x)))))
        rw [AlgEquiv.apply_symm_apply] }
  have hψ_apply : ∀ σ x, ψ σ x = θ.symm (σ (θ x)) := fun _ _ => rfl
  have hψ : Continuous ψ := by
    refine continuous_of_continuousAt_one _ ?_
    rw [ContinuousAt, map_one]
    intro s hs
    obtain ⟨M, hM, hMs⟩ := (krullTopology_mem_nhds_one_iff _ _ s).1 hs
    rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
    have : Module.Free (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion M := Module.Free.of_divisionRing _ M
    let b := Module.finBasis (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion M
    let T : Set (AlgebraicClosure v.Completion) :=
      Set.range fun i => θ (b i : AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion)
    refine ⟨IntermediateField.adjoin v.Completion T, ?_, ?_⟩
    · refine IntermediateField.finiteDimensional_adjoin fun x _ => ?_
      exact Algebra.IsIntegral.isIntegral x
    · intro σ hσ
      apply hMs
      rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
      intro x hx
      have hT : ∀ i, ψ σ (b i : AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion) =
          b i := fun i => by
        rw [hψ_apply, hσ _ (IntermediateField.subset_adjoin v.Completion T ⟨i, rfl⟩), AlgEquiv.symm_apply_apply]
      have hlin : (ψ σ).toAlgHom.toLinearMap ∘ₗ M.val.toLinearMap = M.val.toLinearMap :=
        b.ext fun i => hT i
      exact LinearMap.congr_fun hlin ⟨x, hx⟩
  let f' : Rep.res ψ (galUnitsZ (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion
      (AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion)) ⟶
      galUnitsZ v.Completion (AlgebraicClosure v.Completion) :=
    Rep.ofHom ⟨(MonoidHom.toAdditive (Units.map θ.toRingEquiv.toRingHom.toMonoidHom)).toIntLinearMap,
      fun σ => LinearMap.ext fun x => congrArg Additive.ofMul (Units.ext (by
        change θ (θ.symm (σ (θ ((Additive.toMul x : (AlgebraicClosure _)ˣ) : AlgebraicClosure _)))) =
          σ (θ ((Additive.toMul x : (AlgebraicClosure _)ˣ) : AlgebraicClosure _))
        exact θ.apply_symm_apply _))⟩
  have hinj : Function.Injective (cohomologyMapAlong φ hφ fφ 2).hom := by
    refine cohomologyMapAlong_injective_of_leftInverse φ hφ ψ hψ (fun σ => AlgEquiv.ext fun x => ?_) fφ f'
      (fun a => ?_) 2
    · change θ (θ.symm (σ (θ (θ.symm x)))) = σ x
      rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
    · apply Additive.toMul.injective
      apply Units.ext
      change θ (θ.symm ((Additive.toMul a : (AlgebraicClosure v.Completion)ˣ) : AlgebraicClosure v.Completion)) = _
      exact θ.apply_symm_apply _
  exact quadraticInv_cohomologyMapAlong_of_injective _ _ _ _ hφ fφ hinj _

end

end GroundTheory.ProfCoh
