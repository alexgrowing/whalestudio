import Mathlib
import GroundTheory.AutomorphicForms.GeometricLemmaModular
import GroundTheory.AutomorphicForms.GeometricLemmaCharacters
import GroundTheory.AutomorphicForms.JacquetAdmissible
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa MeasureTheory Measure Topology Set ValuativeRel Measures GLnLocal
open scoped NNReal

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

section Refine

variable {β γ : Fin n → ℕ}

def Refines (β γ : Fin n → ℕ) : Prop := ∀ i j, β j < β i → γ j < γ i

theorem Refines.eq_of_eq (h : Refines β γ) {i j : Fin n} (hij : γ i = γ j) : β i = β j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := h j i hlt
    omega
  · have := h i j hlt
    omega

theorem Refines.refl (β : Fin n → ℕ) : Refines β β := fun _ _ h => h

theorem refines_refineFun (β γ : Fin n → ℕ) : Refines β (refineFun β γ) :=
  fun _ _ h => refineFun_lt h

variable (F) in
theorem Refines.blockUpper_le (h : Refines β γ) : blockUpper F n γ ≤ blockUpper F n β :=
  fun _ hg _ _ hij => hg (h _ _ hij)

variable (F) in
theorem Refines.levi_le (h : Refines β γ) : levi F n γ ≤ levi F n β := by
  intro g hg
  rw [mem_levi] at hg ⊢
  exact fun i j hij => hg i j fun e => hij (h.eq_of_eq e)

variable (F) in
theorem Refines.unipotentRadical_le (h : Refines β γ) :
    unipotentRadical F n β ≤ unipotentRadical F n γ := by
  intro u hu
  obtain ⟨huP, hu1⟩ := mem_unipotentRadical.1 hu
  refine mem_unipotentRadical.2 ⟨fun i j hij => ?_, fun i j hij => hu1 i j (h.eq_of_eq hij)⟩
  rcases lt_trichotomy (β j) (β i) with hb | hb | hb
  · exact huP hb
  · have hne : i ≠ j := fun e => by rw [e] at hij; exact lt_irrefl _ hij
    rw [hu1 i j hb.symm, one_apply_ne hne]
  · exact absurd (h j i hb) (lt_asymm hij)

variable (F) in
theorem Refines.levi_le_leviPar (h : Refines β γ) : levi F n γ ≤ leviPar F n β γ :=
  fun _ hm => ⟨h.levi_le F hm, levi_le_blockUpper hm⟩

variable (F) in
theorem leviPar_le_blockUpper_right : leviPar F n β γ ≤ blockUpper F n γ := inf_le_right

variable (F) in
theorem leviPar_le_blockUpper_left : leviPar F n β γ ≤ blockUpper F n β :=
  fun _ hq => levi_le_blockUpper hq.1

end Refine

section Modular

variable {β γ : Fin n → ℕ}

theorem diagPow_mem_borel (μ : Fin n → ℤ) : Cartan.diagPow F n μ ∈ Iwasawa.borel F n := by
  rw [mem_borel]
  intro i j hij
  have hne : i ≠ j := (ne_of_lt hij).symm
  rw [Cartan.coe_diagPow]
  exact diagonal_apply_ne _ hne

theorem modularCharacter_blockUpper_diagPow (β : Fin n → ℕ) (μ : Fin n → ℤ) :
    modularCharacter (⟨Cartan.diagPow F n μ, levi_le_blockUpper (diagPow_mem_levi μ)⟩ :
      blockUpper F n β) =
      ∏ s : {ij : Fin n × Fin n // β ij.1 < β ij.2},
        modulus ((uniformizer F : F) ^ μ s.1.1) / modulus ((uniformizer F : F) ^ μ s.1.2) := by
  rw [modularCharacter_blockUpper_of_mem_borel' _ (diagPow_mem_borel μ)]
  simp only [Cartan.coe_diagPow, diagonal_apply_eq]

theorem prod_refine_split (h : Refines β γ) (g : Fin n × Fin n → ℝ≥0) :
    ∏ s : {ij : Fin n × Fin n // γ ij.1 < γ ij.2}, g s.1 =
      (∏ s : {ij : Fin n × Fin n // β ij.1 < β ij.2}, g s.1) *
        ∏ s : {ij : Fin n × Fin n // β ij.1 = β ij.2 ∧ γ ij.1 < γ ij.2}, g s.1 := by
  classical
  rw [← Finset.prod_subtype (Finset.univ.filter fun ij : Fin n × Fin n => γ ij.1 < γ ij.2)
      (by simp) g,
    ← Finset.prod_subtype (Finset.univ.filter fun ij : Fin n × Fin n => β ij.1 < β ij.2)
      (by simp) g,
    ← Finset.prod_subtype (Finset.univ.filter fun ij : Fin n × Fin n =>
        β ij.1 = β ij.2 ∧ γ ij.1 < γ ij.2) (by simp) g]
  rw [← Finset.prod_union]
  · congr 1
    ext ij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro hγ
      rcases lt_trichotomy (β ij.1) (β ij.2) with hb | hb | hb
      · exact Or.inl hb
      · exact Or.inr ⟨hb, hγ⟩
      · exact absurd (h _ _ hb) (lt_asymm hγ)
    · rintro (hb | ⟨-, hγ⟩)
      · exact h _ _ hb
      · exact hγ
  · rw [Finset.disjoint_filter]
    intro ij _ h1 h2
    exact h1.ne h2.1

variable (F n β γ) in

def modularRefineLeft : leviPar F n β γ →* ℝ≥0 :=
  (modularCharacter : blockUpper F n γ →* ℝ≥0).comp
    (Subgroup.inclusion (leviPar_le_blockUpper_right F))

variable (F n β γ) in

def modularRefineRight : leviPar F n β γ →* ℝ≥0 :=
  (modularCharacter : blockUpper F n β →* ℝ≥0).comp
    (Subgroup.inclusion (leviPar_le_blockUpper_left F)) *
      (modularCharacter : leviPar F n β γ →* ℝ≥0)

theorem modularCharacter_refine (h : Refines β γ) (q : leviPar F n β γ) :
    modularCharacter (⟨q, q.2.2⟩ : blockUpper F n γ) =
      modularCharacter (⟨q, levi_le_blockUpper q.2.1⟩ : blockUpper F n β) *
        modularCharacter q := by
  obtain ⟨μ, hμ⟩ := exists_diagPow_eq (γ := β) (δ := γ) q
  have h1 := hμ (modularRefineLeft F n β γ) fun k hk =>
    modularCharacter_eq_one_of_mem_integralGL _ hk
  have h2 := hμ (modularRefineRight F n β γ) fun k hk => by
    simp only [modularRefineRight, MonoidHom.mul_apply, MonoidHom.coe_comp, Function.comp_apply]
    rw [modularCharacter_eq_one_of_mem_integralGL _ hk,
      modularCharacter_leviPar_eq_one_of_mem_integralGL _ hk, one_mul]
  change modularRefineLeft F n β γ q = modularRefineRight F n β γ q
  rw [h1, h2]
  simp only [modularRefineLeft, modularRefineRight, MonoidHom.mul_apply, MonoidHom.coe_comp,
    Function.comp_apply]
  have e1 := modularCharacter_blockUpper_diagPow (F := F) γ μ
  have e2 := modularCharacter_blockUpper_diagPow (F := F) β μ
  have e3 := modularCharacter_leviPar_diagPow (F := F) (n := n) (γ := β) (δ := γ) μ
  refine (e1.trans ?_).trans (congrArg₂ (· * ·) e2 e3).symm
  exact prod_refine_split h fun ij =>
    modulus ((uniformizer F : F) ^ μ ij.1) / modulus ((uniformizer F : F) ^ μ ij.2)

variable (F n β γ) in

def sqrtModularLeviPar : leviPar F n β γ →* ℂ where
  toFun q := ((NNReal.sqrt (modularCharacter q) : ℝ) : ℂ)
  map_one' := by simp
  map_mul' p q := by simp [NNReal.sqrt_mul]

variable (F n β γ) in

def invSqrtModularLeviPar : leviPar F n β γ →* ℂ where
  toFun q := (sqrtModularLeviPar F n β γ q)⁻¹
  map_one' := by simp
  map_mul' p q := by rw [map_mul, mul_inv]

theorem sqrtModularLeviPar_ne_zero (q : leviPar F n β γ) : sqrtModularLeviPar F n β γ q ≠ 0 := by
  have h : sqrtModularLeviPar F n β γ q * sqrtModularLeviPar F n β γ q⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  exact left_ne_zero_of_mul_eq_one h

theorem sqrtModularLeviPar_mul_inv (q : leviPar F n β γ) :
    sqrtModularLeviPar F n β γ q * invSqrtModularLeviPar F n β γ q = 1 :=
  mul_inv_cancel₀ (sqrtModularLeviPar_ne_zero q)

theorem sqrtModular_ne_zero {α : Type*} [LinearOrder α] {β : Fin n → α} (p : blockUpper F n β) :
    sqrtModular F n β p ≠ 0 :=
  left_ne_zero_of_mul_eq_one (sqrtModular_mul_invSqrtModular p)

theorem sqrtModular_refine (h : Refines β γ) (q : leviPar F n β γ) :
    sqrtModular F n γ ⟨q, q.2.2⟩ =
      sqrtModular F n β ⟨q, levi_le_blockUpper q.2.1⟩ * sqrtModularLeviPar F n β γ q := by
  show ((NNReal.sqrt (modularCharacter (⟨q, q.2.2⟩ : blockUpper F n γ)) : ℝ) : ℂ) =
    ((NNReal.sqrt (modularCharacter (⟨q, levi_le_blockUpper q.2.1⟩ : blockUpper F n β)) : ℝ) : ℂ) *
      ((NNReal.sqrt (modularCharacter q) : ℝ) : ℂ)
  rw [modularCharacter_refine h q, NNReal.sqrt_mul]
  push_cast
  rfl

theorem invSqrtModular_refine (h : Refines β γ) (q : leviPar F n β γ) :
    invSqrtModular F n γ ⟨q, q.2.2⟩ =
      invSqrtModular F n β ⟨q, levi_le_blockUpper q.2.1⟩ * invSqrtModularLeviPar F n β γ q := by
  show (sqrtModular F n γ ⟨q, q.2.2⟩)⁻¹ =
    (sqrtModular F n β ⟨q, levi_le_blockUpper q.2.1⟩)⁻¹ * (sqrtModularLeviPar F n β γ q)⁻¹
  rw [sqrtModular_refine h q, mul_inv]

theorem sqrtModularLeviPar_of_mem (h : Refines β γ) (q : leviPar F n β γ)
    (hq : (q : GL (Fin n) F) ∈ unipotentRadical F n γ) : sqrtModularLeviPar F n β γ q = 1 := by
  have h1 : sqrtModular F n γ ⟨q, q.2.2⟩ = 1 := sqrtModular_of_mem _ hq
  have h2 : sqrtModular F n β (leviIncl ⟨q, q.2.1⟩) = 1 := sqrtModular_leviIncl_of_mem _ hq
  have h3 := sqrtModular_refine h q
  rw [h1] at h3
  have h2' : sqrtModular F n β ⟨q, levi_le_blockUpper q.2.1⟩ = 1 := h2
  rw [h2', one_mul] at h3
  exact h3.symm

end Modular

section LeviJacquet

variable {β γ : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]

variable (F) in

def Refines.leviToLeviPar (h : Refines β γ) : levi F n γ →* leviPar F n β γ :=
  Subgroup.inclusion (h.levi_le_leviPar F)

theorem Refines.coe_leviToLeviPar (h : Refines β γ) (m : levi F n γ) :
    ((h.leviToLeviPar F m : leviPar F n β γ) : GL (Fin n) F) = m := rfl

variable (F) in

def Refines.leviIncl (h : Refines β γ) : levi F n γ →* levi F n β :=
  Subgroup.inclusion (h.levi_le F)

theorem Refines.coe_leviIncl (h : Refines β γ) (m : levi F n γ) :
    ((h.leviIncl F m : levi F n β) : GL (Fin n) F) = m := rfl

theorem Refines.continuous_leviIncl (h : Refines β γ) : Continuous (h.leviIncl F) :=
  continuous_subtype_val.subtype_mk _

variable (β γ) in

abbrev LeviJacquetModule (σ : Representation ℂ (levi F n β) W) : Type _ :=
  Representation.Coinvariants (σ.comp (leviUnipotent F n β γ).subtype)

def leviJacquetRep (h : Refines β γ) (σ : Representation ℂ (levi F n β) W) :
    Representation ℂ (levi F n γ) (LeviJacquetModule β γ σ) :=
  twist ((invSqrtModularLeviPar F n β γ).comp (h.leviToLeviPar F))
    ((levJacquetAction β σ γ).comp (h.leviToLeviPar F))

theorem leviJacquetRep_mk (h : Refines β γ) (σ : Representation ℂ (levi F n β) W)
    (m : levi F n γ) (w : W) :
    leviJacquetRep h σ m (Representation.Coinvariants.mk _ w) =
      invSqrtModularLeviPar F n β γ (h.leviToLeviPar F m) •
        Representation.Coinvariants.mk _ (σ (h.leviIncl F m) w) := rfl

theorem invSqrtModularLeviPar_of_mem_integralGL (q : leviPar F n β γ)
    (hq : (q : GL (Fin n) F) ∈ integralGL F n) : invSqrtModularLeviPar F n β γ q = 1 := by
  show (((NNReal.sqrt (modularCharacter q) : ℝ) : ℂ))⁻¹ = 1
  rw [modularCharacter_leviPar_eq_one_of_mem_integralGL _ hq]
  simp

theorem isSmooth_leviJacquetRep (h : Refines β γ) {σ : Representation ℂ (levi F n β) W}
    (hσ : IsSmooth σ) : IsSmooth (leviJacquetRep h σ) := by
  intro x
  obtain ⟨w, rfl⟩ := Representation.Coinvariants.mk_surjective _ x
  refine Subgroup.isOpen_mono (H₁ := (stabilizerOf σ w).comap (h.leviIncl F) ⊓
    (integralGL F n).subgroupOf (levi F n γ)) (fun m hm => ?_) ?_
  · obtain ⟨hm1, hm2⟩ := Subgroup.mem_inf.1 hm
    have hw : σ (h.leviIncl F m) w = w := mem_stabilizerOf.1 (Subgroup.mem_comap.1 hm1)
    have hm2' : ((h.leviToLeviPar F m : leviPar F n β γ) : GL (Fin n) F) ∈ integralGL F n := by
      rw [h.coe_leviToLeviPar]
      exact Subgroup.mem_subgroupOf.1 hm2
    have hc := invSqrtModularLeviPar_of_mem_integralGL (h.leviToLeviPar F m) hm2'
    rw [mem_stabilizerOf, leviJacquetRep_mk, hw, hc, one_smul]
  · rw [Subgroup.coe_inf, Subgroup.coe_comap]
    exact ((hσ w).preimage h.continuous_leviIncl).inter
      ((isOpen_integralGL F n).preimage continuous_subtype_val)

end LeviJacquet

section Stages

variable {β γ : Fin n → ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GL (Fin n) F) V)

theorem mk_mk_apply_of_mem (h : Refines β γ) {u : GL (Fin n) F}
    (hu : u ∈ unipotentRadical F n γ) (v : V) :
    Representation.Coinvariants.mk ((jacquetRep F n β π).comp (leviUnipotent F n β γ).subtype)
        (Representation.Coinvariants.mk (π.comp (unipotentRadical F n β).subtype) (π u v)) =
      Representation.Coinvariants.mk _ (Representation.Coinvariants.mk _ v) := by
  obtain ⟨huP, hu1⟩ := mem_unipotentRadical.1 hu
  set p : blockUpper F n β := ⟨u, h.blockUpper_le F huP⟩
  set m := leviProj F n β p
  have hmN : ((m : levi F n β) : GL (Fin n) F) ∈ unipotentRadical F n γ := by
    refine mem_unipotentRadical.2 ⟨fun i j hij => ?_, fun i j hij => ?_⟩
    · show ((m : levi F n β) : GL (Fin n) F) i j = 0
      rw [leviProj_apply]
      split_ifs
      · exact huP hij
      · rfl
    · rw [leviProj_apply, if_pos (h.eq_of_eq hij)]
      exact hu1 i j hij
  have hn' := leviProj_inv_mul_mem p
  have hu' : u = ((m : levi F n β) : GL (Fin n) F) *
      (((leviIncl m)⁻¹ * p : blockUpper F n β) : GL (Fin n) F) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, leviIncl_coe, mul_inv_cancel_left]
  rw [hu', map_mul, Module.End.mul_apply, mk_apply_levi, mk_apply_of_mem π _ hn',
    sqrtModular_leviIncl_of_mem m hmN, one_smul]
  exact Representation.Coinvariants.mk_self_apply
    ((jacquetRep F n β π).comp (leviUnipotent F n β γ).subtype)
    ⟨m, Subgroup.mem_subgroupOf.2 hmN⟩ _

def jacquetStagesInv (h : Refines β γ) :
    JacquetModule F n γ π →ₗ[ℂ] LeviJacquetModule β γ (jacquetRep F n β π) :=
  Representation.Coinvariants.lift _
    (Representation.Coinvariants.mk _ ∘ₗ Representation.Coinvariants.mk _)
    fun u => LinearMap.ext fun v => mk_mk_apply_of_mem π h u.2 v

def jacquetStagesMap (h : Refines β γ) :
    LeviJacquetModule β γ (jacquetRep F n β π) →ₗ[ℂ] JacquetModule F n γ π :=
  Representation.Coinvariants.lift _
    (Representation.Coinvariants.lift _ (Representation.Coinvariants.mk _)
      fun u => LinearMap.ext fun v => mk_apply_of_mem π _ (h.unipotentRadical_le F u.2) v)
    fun u => by
      refine Representation.Coinvariants.hom_ext (LinearMap.ext fun v => ?_)
      have hu : ((u : levi F n β) : GL (Fin n) F) ∈ unipotentRadical F n γ :=
        Subgroup.mem_subgroupOf.1 u.2
      have hinv : invSqrtModular F n β (leviIncl (u : levi F n β)) = 1 := by
        show (sqrtModular F n β (leviIncl (u : levi F n β)))⁻¹ = 1
        rw [sqrtModular_leviIncl_of_mem _ hu, inv_one]
      simp only [LinearMap.coe_comp, Function.comp_apply, MonoidHom.coe_comp,
        Subgroup.coe_subtype]
      rw [jacquetRep_mk, hinv, one_smul, Representation.Coinvariants.lift_mk,
        Representation.Coinvariants.lift_mk]
      exact mk_apply_of_mem π _ hu v

theorem jacquetStagesMap_mk_mk (h : Refines β γ) (v : V) :
    jacquetStagesMap π h (Representation.Coinvariants.mk _ (Representation.Coinvariants.mk _ v)) =
      Representation.Coinvariants.mk _ v := rfl

theorem jacquetStagesInv_mk (h : Refines β γ) (v : V) :
    jacquetStagesInv π h (Representation.Coinvariants.mk _ v) =
      Representation.Coinvariants.mk _ (Representation.Coinvariants.mk _ v) := rfl

def jacquetStagesLinearEquiv (h : Refines β γ) :
    LeviJacquetModule β γ (jacquetRep F n β π) ≃ₗ[ℂ] JacquetModule F n γ π :=
  LinearEquiv.ofLinearMap (f := jacquetStagesMap π h) (g := jacquetStagesInv π h)
    (Representation.Coinvariants.hom_ext (LinearMap.ext fun _ => rfl))
    (Representation.Coinvariants.hom_ext (Representation.Coinvariants.hom_ext
      (LinearMap.ext fun _ => rfl)))

def jacquetStages (h : Refines β γ) :
    (leviJacquetRep h (jacquetRep F n β π)).Equiv (jacquetRep F n γ π) :=
  Representation.Equiv.mk (jacquetStagesLinearEquiv π h) fun m => by
    refine Representation.Coinvariants.hom_ext (Representation.Coinvariants.hom_ext
      (LinearMap.ext fun v => ?_))
    have key := invSqrtModular_refine h (h.leviToLeviPar F m)
    simp only [LinearMap.coe_comp, Function.comp_apply]
    show jacquetStagesMap π h (leviJacquetRep h (jacquetRep F n β π) m
        (Representation.Coinvariants.mk _ (Representation.Coinvariants.mk _ v))) =
      jacquetRep F n γ π m (Representation.Coinvariants.mk _ v)
    rw [leviJacquetRep_mk, jacquetRep_mk]
    simp only [map_smul, jacquetStagesMap_mk_mk, jacquetRep_mk, smul_smul]
    congr 1
    rw [mul_comm]
    exact key.symm

theorem jacquetStages_mk (h : Refines β γ) (v : V) :
    jacquetStages π h (Representation.Coinvariants.mk _ (Representation.Coinvariants.mk _ v)) =
      Representation.Coinvariants.mk _ v := rfl

end Stages

end Parabolic

end GroundTheory.Automorphic
