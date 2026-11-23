import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.Invariants
import GroundTheory.GlobalFields.IdeleClassGroup.InvariantsGalois
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleCohomology
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global GroundTheory.Global.AdeleBaseChange
  FiniteSubfield IdeleLimit

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable (K : FiniteSubfield)

abbrev GLevel : Type := {F : FiniteSubfield // K ≤ F ∧ F.1.fixingSubgroup.Normal}

instance isGalois_rat_algebraicClosure : IsGalois ℚ ℚ̄ := IsAlgClosure.isGalois ℚ ℚ̄

theorem normal_fixingSubgroup_galoisClosure (S : FiniteSubfield) :
    (galoisClosure S).1.fixingSubgroup.Normal := by
  show (normalClosure ℚ S.1 ℚ̄).fixingSubgroup.Normal
  haveI : IsGalois ℚ (normalClosure ℚ S.1 ℚ̄) := IsGalois.normalClosure ℚ S.1 ℚ̄
  exact IsGalois.fixingSubgroup_normal_of_isGalois _

namespace GLevel

variable {K}

instance (p : GLevel K) : Fact (K ≤ p.1) := ⟨p.2.1⟩

instance (p : GLevel K) : p.1.1.fixingSubgroup.Normal := p.2.2

theorem le_def {p q : GLevel K} : p ≤ q ↔ p.1 ≤ q.1 := Iff.rfl

instance : IsDirectedOrder (GLevel K) where
  directed p q := by
    let S : FiniteSubfield := ⟨p.1.1 ⊔ q.1.1, inferInstance⟩
    refine ⟨⟨galoisClosure S, p.2.1.trans ((show p.1.1 ≤ p.1.1 ⊔ q.1.1 from le_sup_left).trans
      (le_galoisClosure S)), normal_fixingSubgroup_galoisClosure S⟩, ?_, ?_⟩
    · exact (show p.1.1 ≤ p.1.1 ⊔ q.1.1 from le_sup_left).trans (le_galoisClosure S)
    · exact (show q.1.1 ≤ p.1.1 ⊔ q.1.1 from le_sup_right).trans (le_galoisClosure S)

theorem exists_ge (p q : GLevel K) : ∃ r : GLevel K, p ≤ r ∧ q ≤ r := by
  let S : FiniteSubfield := ⟨p.1.1 ⊔ q.1.1, inferInstance⟩
  refine ⟨⟨galoisClosure S, p.2.1.trans ((show p.1.1 ≤ p.1.1 ⊔ q.1.1 from le_sup_left).trans
    (le_galoisClosure S)), normal_fixingSubgroup_galoisClosure S⟩, ?_, ?_⟩
  · exact (show p.1.1 ≤ p.1.1 ⊔ q.1.1 from le_sup_left).trans (le_galoisClosure S)
  · exact (show q.1.1 ≤ p.1.1 ⊔ q.1.1 from le_sup_right).trans (le_galoisClosure S)

instance : Nonempty (GLevel K) :=
  ⟨⟨galoisClosure K, le_galoisClosure K, normal_fixingSubgroup_galoisClosure K⟩⟩

theorem exists_le (E : FiniteSubfield) : ∃ p : GLevel K, E ≤ p.1 := by
  let S : FiniteSubfield := ⟨K.1 ⊔ E.1, inferInstance⟩
  exact ⟨⟨galoisClosure S, (show K.1 ≤ K.1 ⊔ E.1 from le_sup_left).trans (le_galoisClosure S),
    normal_fixingSubgroup_galoisClosure S⟩,
    (show E.1 ≤ K.1 ⊔ E.1 from le_sup_right).trans (le_galoisClosure S)⟩

end GLevel

abbrev limitRep : Rep ℤ K.1.fixingSubgroup := Rep.res K.1.fixingSubgroup.subtype IdeleLimit.rep

variable {K}

section Level

variable {F : FiniteSubfield} [Fact (K ≤ F)]

instance normal_subgroupOf [F.1.fixingSubgroup.Normal] :
    (F.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal :=
  Subgroup.Normal.subgroupOf inferInstance _

instance [F.1.fixingSubgroup.Normal] : IsGalois K.1 F.1 := isGalois_of_normal

theorem continuous_restrictHom [F.1.fixingSubgroup.Normal] :
    Continuous (restrictHom : K.1.fixingSubgroup →* (F.1 ≃ₐ[K.1] F.1)) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, Filter.tendsto_def]
  intro s hs
  have hopen : IsOpen ((F.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup : Subgroup _) :
      Set K.1.fixingSubgroup) :=
    F.1.fixingSubgroup_isOpen.preimage continuous_subtype_val
  filter_upwards [hopen.mem_nhds (one_mem _)] with g hg
  have hg' : restrictHom (E := F) g = 1 := by
    rw [← MonoidHom.mem_ker, ker_restrictHom]
    exact hg
  change restrictHom (E := F) g ∈ s
  rw [hg', ← map_one (restrictHom (F := K) (E := F))]
  exact mem_of_mem_nhds hs

theorem smul_of_restrictHom [F.1.fixingSubgroup.Normal] (g : K.1.fixingSubgroup) (x : IdeleGroup F.1) :
    (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) • of F x = of F (restrictHom (E := F) g • x) := by
  rw [smul_idele_eq_ideleEquiv]
  exact smul_of_eq_of_ideleEquiv _ _ (fun _ ↦ rfl) x

variable (K F) in

def levelMor [F.1.fixingSubgroup.Normal] : Rep.res (restrictHom (F := K) (E := F)) (ideleRep K.1 F.1) ⟶ limitRep K :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (of F)).toIntLinearMap, fun g => LinearMap.ext fun x =>
    congrArg Additive.ofMul (smul_of_restrictHom g x.toMul).symm⟩

@[simp]
theorem levelMor_hom_apply [F.1.fixingSubgroup.Normal] (x : Additive (IdeleGroup F.1)) :
    (levelMor K F).hom x = Additive.ofMul (of F x.toMul) :=
  rfl

variable (K F) in

def levelInfl [F.1.fixingSubgroup.Normal] (n : ℕ) : cohomology (ideleRep K.1 F.1) n ⟶ cohomology (limitRep K) n :=
  cohomologyMapAlong restrictHom continuous_restrictHom (levelMor K F) n

end Level

end

end GroundTheory.ProfCoh
