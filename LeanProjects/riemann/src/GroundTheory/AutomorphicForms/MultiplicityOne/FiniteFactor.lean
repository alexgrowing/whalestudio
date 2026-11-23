import Mathlib
import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteLevel
import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteLevelGroups
import GroundTheory.AutomorphicForms.MultiplicityOne.OpenSubgroupRep

open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain

namespace GroundTheory.Automorphic

noncomputable section

namespace MultiplicityOne

set_option linter.unusedSectionVars false

open Reduction AutomorphicForm RightCosetSpace CuspidalSpectrum

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

variable (K n) in

def finComp : normOneGL K n →* AdelicGLn.FiniteAdelicGL K n :=
  (MonoidHom.snd _ _).comp ((AdelicGLn.prodEquiv K n).toMonoidHom.comp (normOneGL K n).subtype)

theorem finComp_apply (x : normOneGL K n) :
    finComp K n x = (AdelicGLn.prodEquiv K n (x : AdelicGLn.AdelicGL K n)).2 := rfl

theorem continuous_finComp : Continuous (finComp K n) :=
  continuous_snd.comp ((AdelicGLn.prodEquiv K n).continuous.comp continuous_subtype_val)

theorem finComp_archProj (A : ArchUnits K n) : finComp K n (archProj K n A) = 1 := by
  rw [finComp_apply, coe_archProj, map_mul, map_inv]
  have h1 : (AdelicGLn.prodEquiv K n (archIncl K n A)).2 = 1 := by
    show (AdelicGLn.prodEquiv K n (infEmb K n ⟨A, trivial⟩)).2 = 1
    rw [prodEquiv_infEmb]
  have h2 : (AdelicGLn.prodEquiv K n (centralSection K n
      (detModule K n (archIncl K n A)))).2 = 1 := by
    rw [centralSection, MonoidHom.comp_apply, scalarUnits_apply]
    exact prodEquiv_diagUnits_posIdele_snd (K := K) (n := n)
      (fun _ => ((rpowHom ((n * Module.finrank ℚ K : ℝ))⁻¹ (detModule K n (archIncl K n A)) :
        {r : ℝ // 0 < r}) : ℝ)) (fun _ => (rpowHom _ _).2)
  simp only [Prod.snd_mul, Prod.snd_inv, h1, h2, inv_one, mul_one]

theorem finComp_finProj (u : AdelicGLn.FiniteAdelicGL K n) : finComp K n (finProj K n u) = u := by
  rw [finComp_apply, coe_finProj, map_mul, map_inv]
  have h1 : (AdelicGLn.prodEquiv K n (finEmb K n u)).2 = u := by rw [prodEquiv_finEmb]
  have h2 : (AdelicGLn.prodEquiv K n (centralSection K n
      (detModule K n (finEmb K n u)))).2 = 1 := by
    rw [centralSection, MonoidHom.comp_apply, scalarUnits_apply]
    exact prodEquiv_diagUnits_posIdele_snd (K := K) (n := n)
      (fun _ => ((rpowHom ((n * Module.finrank ℚ K : ℝ))⁻¹ (detModule K n (finEmb K n u)) :
        {r : ℝ // 0 < r}) : ℝ)) (fun _ => (rpowHom _ _).2)
  simp only [Prod.snd_mul, Prod.snd_inv, h1, h2, inv_one, mul_one]

variable (K n) in

def levelSubgroup (U : Subgroup (AdelicGLn.FiniteAdelicGL K n)) : Subgroup (normOneGL K n) :=
  U.comap (finComp K n)

theorem mem_levelSubgroup {U : Subgroup (AdelicGLn.FiniteAdelicGL K n)} {x : normOneGL K n} :
    x ∈ levelSubgroup K n U ↔ finComp K n x ∈ U := Iff.rfl

theorem isOpen_levelSubgroup {U : Subgroup (AdelicGLn.FiniteAdelicGL K n)}
    (hU : IsOpen (U : Set (AdelicGLn.FiniteAdelicGL K n))) :
    IsOpen (levelSubgroup K n U : Set (normOneGL K n)) :=
  hU.preimage continuous_finComp

theorem archProj_mem_levelSubgroup (U : Subgroup (AdelicGLn.FiniteAdelicGL K n)) (A : ArchUnits K n) :
    archProj K n A ∈ levelSubgroup K n U := by
  rw [mem_levelSubgroup, finComp_archProj]
  exact U.one_mem

theorem finProj_mem_levelSubgroup {U : Subgroup (AdelicGLn.FiniteAdelicGL K n)}
    {u : AdelicGLn.FiniteAdelicGL K n} (hu : u ∈ U) : finProj K n u ∈ levelSubgroup K n U := by
  rw [mem_levelSubgroup, finComp_finProj]
  exact hu

theorem exists_of_mem_levelSubgroup {U : Subgroup (AdelicGLn.FiniteAdelicGL K n)}
    {x : normOneGL K n} (hx : x ∈ levelSubgroup K n U) :
    ∃ (A : ArchUnits K n) (u : AdelicGLn.FiniteAdelicGL K n), u ∈ U ∧
      archProj K n A * finProj K n u = x := by
  obtain ⟨A, u, rfl⟩ := exists_archProj_mul_finProj x
  refine ⟨A, u, ?_, rfl⟩
  have := (mem_levelSubgroup).1 hx
  rwa [map_mul, finComp_archProj, finComp_finProj, one_mul] at this

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def fixedSubspace (σ : UnitaryRep (normOneGL K n) H) (U : Subgroup (AdelicGLn.FiniteAdelicGL K n)) :
    Submodule ℂ H where
  carrier := {v | ∀ u ∈ U, σ (finProj K n u) v = v}
  add_mem' hv hw u hu := by rw [map_add, hv u hu, hw u hu]
  zero_mem' u _ := map_zero _
  smul_mem' c v hv u hu := by rw [map_smul, hv u hu]

theorem mem_fixedSubspace {σ : UnitaryRep (normOneGL K n) H}
    {U : Subgroup (AdelicGLn.FiniteAdelicGL K n)} {v : H} :
    v ∈ fixedSubspace σ U ↔ ∀ u ∈ U, σ (finProj K n u) v = v := Iff.rfl

theorem isClosed_fixedSubspace (σ : UnitaryRep (normOneGL K n) H)
    (U : Subgroup (AdelicGLn.FiniteAdelicGL K n)) :
    IsClosed (fixedSubspace σ U : Set H) := by
  have e : (fixedSubspace σ U : Set H) =
      ⋂ u ∈ U, {v | σ (finProj K n u) v = v} := by
    ext v
    simp only [SetLike.mem_coe, mem_fixedSubspace, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [e]
  exact isClosed_biInter fun u _ => isClosed_eq (σ (finProj K n u)).continuous continuous_id

theorem isInvariant_fixedSubspace (σ : UnitaryRep (normOneGL K n) H)
    (U : Subgroup (AdelicGLn.FiniteAdelicGL K n)) :
    (σ.compHom (levelSubgroup K n U).subtype continuous_subtype_val).IsInvariant
      (fixedSubspace σ U) := by
  rintro ⟨x, hx⟩ v hv u hu
  obtain ⟨A, u', hu', rfl⟩ := exists_of_mem_levelSubgroup hx
  show σ (finProj K n u) (σ (archProj K n A * finProj K n u') v) = σ (archProj K n A * finProj K n u') v
  have e : finProj K n u * (archProj K n A * finProj K n u') =
      archProj K n A * finProj K n u' * finProj K n (u'⁻¹ * u * u') := by
    rw [map_mul, map_mul, map_inv, ← mul_assoc, finProj_mul_archProj_comm]
    group
  rw [← UnitaryRep.map_mul_apply, e, UnitaryRep.map_mul_apply,
    hv _ (U.mul_mem (U.mul_mem (U.inv_mem hu') hu) hu')]

variable (σ : UnitaryRep (normOneGL K n) H) (U : Subgroup (AdelicGLn.FiniteAdelicGL K n))

instance : CompleteSpace (fixedSubspace σ U) := (isClosed_fixedSubspace σ U).completeSpace_coe

def levelRep : UnitaryRep (levelSubgroup K n U) (fixedSubspace σ U) :=
  (σ.compHom (levelSubgroup K n U).subtype continuous_subtype_val).restrict (fixedSubspace σ U)
    (isInvariant_fixedSubspace σ U)

@[simp] theorem coe_levelRep_apply (x : levelSubgroup K n U) (v : fixedSubspace σ U) :
    ((levelRep σ U x v : fixedSubspace σ U) : H) = σ x v := rfl

variable {μ : Measure (normOneGL K n)} [μ.IsHaarMeasure]

set_option maxHeartbeats 4000000 in

theorem isCompactOperator_levelRep (hσ : σ.IsIrreducible) (T : cuspIntertwiners μ σ) (hT0 : T ≠ 0)
    (hU : IsOpen (U : Set (AdelicGLn.FiniteAdelicGL K n)))
    (f : CompactlySupportedContinuousMap (levelSubgroup K n U) ℂ) :
    haveI := UnitaryRep.isFiniteMeasureOnCompacts_comap μ (isOpen_levelSubgroup (K := K) (n := n) hU)
    IsCompactOperator ((levelRep σ U).integrated (μ.comap ((↑) : levelSubgroup K n U → normOneGL K n))
      (UnitaryRep.ccToL1 (μ.comap ((↑) : levelSubgroup K n U → normOneGL K n)) f)) := by
  have := UnitaryRep.isFiniteMeasureOnCompacts_comap μ (isOpen_levelSubgroup (K := K) (n := n) hU)
  refine UnitaryRep.isCompactOperator_restrict_integrated _ _ (isClosed_fixedSubspace σ U)
    (isInvariant_fixedSubspace σ U) _ ?_
  exact UnitaryRep.isCompactOperator_compHom_subtype σ μ (isOpen_levelSubgroup hU)
    (isCompactOperator_integrated_of_irreducible hσ T hT0) f

end MultiplicityOne

end

end GroundTheory.Automorphic
