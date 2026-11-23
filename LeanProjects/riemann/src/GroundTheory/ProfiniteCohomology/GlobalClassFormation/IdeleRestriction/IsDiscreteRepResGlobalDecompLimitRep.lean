import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleRestriction
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalResConj
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain IdeleLimit
  GroundTheory.Global.IdeleGroup GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange

open scoped NumberField.LiesOver NumberField.AdeleRing

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield}

instance isDiscreteRep_res_globalDecomp_limitRep (Kv : Type) {Ωv : Type} [Field Kv] [Field Ωv] [Algebra K.1 Kv]
    [Algebra Kv Ωv] [Algebra K.1 Ωv] [IsScalarTower K.1 Kv Ωv] (ι : ℚ̄ →ₐ[K.1] Ωv) :
    IsDiscreteRep (Rep.res (globalDecomp Kv ι) (limitRep K)) :=
  IsDiscreteRep.res (continuous_globalDecomp Kv ι) _

section Finite

variable {v : HeightOneSpectrum (𝓞 K.1)} (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1))

theorem completionEmbedding_eq_of_algebraMap (F : FiniteSubfield) [Fact (K ≤ F)] (u : PlacesOver F.1 v)
    (j : u.1.adicCompletion F.1 →ₐ[v.adicCompletion K.1] AlgebraicClosure (v.adicCompletion K.1))
    (hj : ∀ x : F.1, j (algebraMap F.1 _ x) = ι x) (a : 𝔸[F.1]) :
    j (a.2 u.1) = completionEmbedding ι F (a.2 (placeOfEmbedding ι F).1) := by
  have h := eq_placeOfEmbedding ι F j hj
  subst h
  rw [algHom_ext_adicCompletion F (f := j) (g := completionEmbedding ι F)
    fun x => by rw [hj, completionEmbedding_algebraMap]]

set_option maxHeartbeats 2000000 in

theorem idelesProj_comp (g : K.1.fixingSubgroup) (z : IdeleLimit) :
    idelesProj (ι.comp (fixingSubgroupEquiv K.1 g : ℚ̄ →ₐ[K.1] ℚ̄)) z = idelesProj ι ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) • z) := by
  obtain ⟨F, x, rfl⟩ := exists_of z
  obtain ⟨p, hp⟩ := GLevel.exists_le (K := K) F
  rw [← of_ideleMap hp x]
  generalize ideleMap hp x = y
  rw [smul_of_restrictHom]
  set r : p.1.1 ≃ₐ[K.1] p.1.1 := restrictHom (E := p.1) g with hr
  set w := placeOfEmbedding ι p.1 with hw
  apply Units.ext
  rw [coe_idelesProj_of, coe_idelesProj_of, coe_smul_idele,
    smul_snd_eq_galHom r (y : 𝔸[p.1.1]) (r⁻¹ • w).1 w.1 (eq_smul_inv_smul v r w)]
  let j : (r⁻¹ • w).1.adicCompletion p.1.1 →ₐ[v.adicCompletion K.1] AlgebraicClosure (v.adicCompletion K.1) :=
    (completionEmbedding ι p.1).comp (galEquiv v r (r⁻¹ • w).1 w.1 (eq_smul_inv_smul v r w)).toAlgHom
  have hj : ∀ x : p.1.1, j (algebraMap p.1.1 _ x) = (ι.comp (fixingSubgroupEquiv K.1 g : ℚ̄ →ₐ[K.1] ℚ̄)) x := by
    intro x
    change completionEmbedding ι p.1 (galEquiv v r (r⁻¹ • w).1 w.1 (eq_smul_inv_smul v r w)
      (algebraMap p.1.1 _ x)) = ι ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) (x : ℚ̄))
    rw [galEquiv_algebraMap, completionEmbedding_algebraMap, hr, coe_restrictHom_apply]
  exact (completionEmbedding_eq_of_algebraMap _ p.1 (r⁻¹ • w) j hj (y : 𝔸[p.1.1])).symm

set_option maxHeartbeats 2000000 in

theorem idelesLocalRes_comp (g : K.1.fixingSubgroup) (n : ℕ) :
    idelesLocalRes (ι.comp (fixingSubgroupEquiv K.1 g : ℚ̄ →ₐ[K.1] ℚ̄)) n = idelesLocalRes ι n := by
  set ι' := ι.comp (fixingSubgroupEquiv K.1 g : ℚ̄ →ₐ[K.1] ℚ̄)
  have hconj := cohomologyMapAlong_conj (limitRep K) (continuous_globalDecomp (v.adicCompletion K.1) ι)
    (continuous_globalDecomp (v.adicCompletion K.1) ι') g (globalDecomp_comp (v.adicCompletion K.1) ι g) n
  have e1 : idelesLocalRes ι' n =
      cohomologyMapAlong (globalDecomp (v.adicCompletion K.1) ι') (continuous_globalDecomp (v.adicCompletion K.1) ι') (𝟙 _) n ≫
      cohomologyMapAlong (MonoidHom.id _) continuous_id (idelesLocalMor ι') n := by
    rw [idelesLocalRes, ← cohomologyMapAlong_comp]
    rfl
  have e2 : idelesLocalRes ι n =
      cohomologyMapAlong (globalDecomp (v.adicCompletion K.1) ι) (continuous_globalDecomp (v.adicCompletion K.1) ι) (𝟙 _) n ≫
      cohomologyMapAlong (MonoidHom.id _) continuous_id (idelesLocalMor ι) n := by
    rw [idelesLocalRes, ← cohomologyMapAlong_comp]
    rfl
  rw [e1, hconj, Category.assoc, ← cohomologyMapAlong_comp, e2]
  congr 1
  refine cohomologyMapAlong_congr _ _ _ _ rfl (fun (a : Additive IdeleLimit) => ?_) n
  apply Additive.toMul.injective
  change idelesProj ι' (((g⁻¹ : K.1.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄) • a.toMul) = idelesProj ι a.toMul
  rw [idelesProj_comp, smul_smul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, one_smul]

theorem idelesLocalRes_eq_of_algHom (ι ι' : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1)) (n : ℕ) :
    idelesLocalRes ι' n = idelesLocalRes ι n := by
  obtain ⟨g, hg⟩ := exists_eq_comp_of_normal ι ι'
  have : ι' = ι.comp (fixingSubgroupEquiv K.1 ((fixingSubgroupEquiv K.1).symm g) : ℚ̄ →ₐ[K.1] ℚ̄) := by
    rw [MulEquiv.apply_symm_apply]
    exact hg
  rw [this, idelesLocalRes_comp]

end Finite

section Infinite

variable {v : InfinitePlace K.1} (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion)

theorem infCompletionEmbedding_eq_of_algebraMap (F : FiniteSubfield) [Fact (K ≤ F)] (u : v.placesOver F.1)
    (j : (u : InfinitePlace F.1).Completion →ₐ[v.Completion] AlgebraicClosure v.Completion)
    (hj : ∀ x : F.1, j (algebraMap F.1 _ x) = ι x) (a : 𝔸[F.1]) :
    j (a.1 u) = infCompletionEmbedding ι F (a.1 (infPlaceOfEmbedding ι F : InfinitePlace F.1)) := by
  have h := eq_infPlaceOfEmbedding ι F j hj
  subst h
  rw [algHom_ext_infCompletion F (f := j) (g := infCompletionEmbedding ι F)
    fun x => by rw [hj, infCompletionEmbedding_algebraMap]]

set_option maxHeartbeats 2000000 in

theorem infIdelesProj_comp (g : K.1.fixingSubgroup) (z : IdeleLimit) :
    infIdelesProj (ι.comp (fixingSubgroupEquiv K.1 g : ℚ̄ →ₐ[K.1] ℚ̄)) z =
      infIdelesProj ι ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) • z) := by
  obtain ⟨F, x, rfl⟩ := exists_of z
  obtain ⟨p, hp⟩ := GLevel.exists_le (K := K) F
  rw [← of_ideleMap hp x]
  generalize ideleMap hp x = y
  rw [smul_of_restrictHom]
  set r : p.1.1 ≃ₐ[K.1] p.1.1 := restrictHom (E := p.1) g with hr
  set w := infPlaceOfEmbedding ι p.1 with hw
  apply Units.ext
  rw [coe_infIdelesProj_of, coe_infIdelesProj_of, coe_smul_idele, smul_fst r (y : 𝔸[p.1.1])]
  have hcomap : (w : InfinitePlace p.1.1).comap ((r : p.1.1 ≃+* p.1.1) : p.1.1 →+* p.1.1) =
      r⁻¹ • (w : InfinitePlace p.1.1) :=
    AdeleBaseChange.comap_eq_inv_smul r w
  have hu : ((w : InfinitePlace p.1.1).comap ((r : p.1.1 ≃+* p.1.1) : p.1.1 →+* p.1.1)).LiesOver v := by
    rw [GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq, hcomap,
      GroundTheory.Global.InfinitePlace.comap_smul_algebraMap,
      ← GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq]
    exact w.2
  let u : v.placesOver p.1.1 := ⟨_, hu⟩
  let j : (u : InfinitePlace p.1.1).Completion →ₐ[v.Completion] AlgebraicClosure v.Completion :=
    (infCompletionEmbedding ι p.1).comp
      { AdeleBaseChange.infiniteCompletionMap (r : p.1.1 ≃+* p.1.1) w with
        commutes' := infiniteCompletionMap_algebraMap_completion p.1 r w }
  have hj : ∀ x : p.1.1, j (algebraMap p.1.1 _ x) = (ι.comp (fixingSubgroupEquiv K.1 g : ℚ̄ →ₐ[K.1] ℚ̄)) x := by
    intro x
    change infCompletionEmbedding ι p.1 (AdeleBaseChange.infiniteCompletionMap (r : p.1.1 ≃+* p.1.1) w
      (algebraMap p.1.1 _ x)) = ι ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) (x : ℚ̄))
    rw [AdeleBaseChange.infiniteCompletionMap_algebraMap, infCompletionEmbedding_algebraMap, AlgEquiv.coe_ringEquiv,
      hr, coe_restrictHom_apply]
  exact (infCompletionEmbedding_eq_of_algebraMap _ p.1 u j hj (y : 𝔸[p.1.1])).symm

set_option maxHeartbeats 2000000 in

theorem infIdelesLocalRes_comp (g : K.1.fixingSubgroup) (n : ℕ) :
    infIdelesLocalRes (ι.comp (fixingSubgroupEquiv K.1 g : ℚ̄ →ₐ[K.1] ℚ̄)) n = infIdelesLocalRes ι n := by
  set ι' := ι.comp (fixingSubgroupEquiv K.1 g : ℚ̄ →ₐ[K.1] ℚ̄)
  have hconj := cohomologyMapAlong_conj (limitRep K) (continuous_globalDecomp v.Completion ι)
    (continuous_globalDecomp v.Completion ι') g (globalDecomp_comp v.Completion ι g) n
  have e1 : infIdelesLocalRes ι' n =
      cohomologyMapAlong (globalDecomp v.Completion ι') (continuous_globalDecomp v.Completion ι') (𝟙 _) n ≫
      cohomologyMapAlong (MonoidHom.id _) continuous_id (infIdelesLocalMor ι') n := by
    rw [infIdelesLocalRes, ← cohomologyMapAlong_comp]
    rfl
  have e2 : infIdelesLocalRes ι n =
      cohomologyMapAlong (globalDecomp v.Completion ι) (continuous_globalDecomp v.Completion ι) (𝟙 _) n ≫
      cohomologyMapAlong (MonoidHom.id _) continuous_id (infIdelesLocalMor ι) n := by
    rw [infIdelesLocalRes, ← cohomologyMapAlong_comp]
    rfl
  rw [e1, hconj, Category.assoc, ← cohomologyMapAlong_comp, e2]
  congr 1
  refine cohomologyMapAlong_congr _ _ _ _ rfl (fun (a : Additive IdeleLimit) => ?_) n
  apply Additive.toMul.injective
  change infIdelesProj ι' (((g⁻¹ : K.1.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄) • a.toMul) = infIdelesProj ι a.toMul
  rw [infIdelesProj_comp, smul_smul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, one_smul]

theorem infIdelesLocalRes_eq_of_algHom (ι ι' : ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion) (n : ℕ) :
    infIdelesLocalRes ι' n = infIdelesLocalRes ι n := by
  obtain ⟨g, hg⟩ := exists_eq_comp_of_normal ι ι'
  have : ι' = ι.comp (fixingSubgroupEquiv K.1 ((fixingSubgroupEquiv K.1).symm g) : ℚ̄ →ₐ[K.1] ℚ̄) := by
    rw [MulEquiv.apply_symm_apply]
    exact hg
  rw [this, infIdelesLocalRes_comp]

end Infinite

end

end GroundTheory.ProfCoh
