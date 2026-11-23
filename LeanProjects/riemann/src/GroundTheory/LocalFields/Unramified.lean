import Mathlib
import GroundTheory.LocalFields.Interface
import GroundTheory.LocalFields.Integers
import GroundTheory.LocalFields.Uniqueness
import GroundTheory.LocalFields.IntermediateField
import GroundTheory.LocalFields.UnramifiedDefs
import GroundTheory.LocalFields.UnramifiedHensel

noncomputable section

open ValuativeRel IsLocalRing Polynomial
open scoped _root_.IntermediateField

namespace GroundTheory.LocalField

section Generator

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem isUnit_aeval_derivative_of_separable (P : 𝒪[K][X])
    (hP : (P.map (residue 𝒪[K])).Separable) (x : 𝒪[L]) (hx : aeval x P = 0) :
    IsUnit (aeval x (derivative P)) := by
  rw [← residue_ne_zero_iff_isUnit, residue_aeval K L (fun _ ↦ rfl), ← derivative_map]
  refine hP.aeval_derivative_ne_zero ?_
  rw [← residue_aeval K L (fun _ ↦ rfl), hx, map_zero]

theorem IsUnramified.exists_generator [IsUnramified K L] :
    ∃ (β : 𝒪[L]) (P : 𝒪[K][X]), P.Monic ∧ aeval β P = 0 ∧ (P.map (residue 𝒪[K])).Separable ∧
      IsUnit (aeval β (derivative P)) ∧ K⟮(β : L)⟯ = ⊤ := by
  obtain ⟨β, P, hPm, hβ, hsep, -, hdeg, -⟩ := exists_unramified_adjoin K L
  refine ⟨β, P, hPm, hβ, hsep, isUnit_aeval_derivative_of_separable K L P hsep β hβ, ?_⟩
  refine IntermediateField.eq_of_le_of_finrank_eq le_top ?_
  rw [hdeg, IntermediateField.finrank_top', IsUnramified.residueDegree_eq_finrank K L]

end Generator

section Etale

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem map_maximalIdeal_eq_iff :
    (maximalIdeal 𝒪[K]).map (algebraMap 𝒪[K] 𝒪[L]) = maximalIdeal 𝒪[L] ↔ IsUnramified K L := by
  rw [map_maximalIdeal K L, isUnramified_iff]
  constructor
  · intro h
    have hpos := ramificationIndex_pos K L
    by_contra hne
    have h2 : 2 ≤ ramificationIndex K L := by omega
    have hL : maximalIdeal 𝒪[L] ≠ ⊥ := maximalIdeal_ne_bot L
    have hlt := Ideal.pow_succ_lt_pow hL 1
    have hle : maximalIdeal 𝒪[L] ^ 1 ≤ maximalIdeal 𝒪[L] ^ (1 + 1) :=
      calc maximalIdeal 𝒪[L] ^ 1 = maximalIdeal 𝒪[L] ^ ramificationIndex K L := by
            rw [pow_one, h]
        _ ≤ maximalIdeal 𝒪[L] ^ (1 + 1) := Ideal.pow_le_pow_right h2
    exact absurd hle (not_le_of_gt hlt)
  · intro h
    rw [h, pow_one]

end Etale

section Maximal

variable (K L : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]

def maximalUnramified : IntermediateField K L :=
  sSup {E : IntermediateField K L | IsUnramified K E}

theorem le_maximalUnramified (E : IntermediateField K L) [IsUnramified K E] :
    E ≤ maximalUnramified K L :=
  le_sSup (show IsUnramified K E from inferInstance)

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [FiniteDimensional K L]

variable {K L} in

theorem IsUnramified.of_le {E F : IntermediateField K L} (h : E ≤ F) [IsUnramified K F] :
    IsUnramified K E := by
  let : Algebra E F := (IntermediateField.inclusion h).toRingHom.toAlgebra
  have : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : ValuativeExtension E F := valuativeExtension_algHom (K := K) (IntermediateField.inclusion h)
  have : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite K E F
  exact IsUnramified.of_tower_left K E F

theorem exists_generator_of_isUnramified (E : IntermediateField K L) [IsUnramified K E] :
    ∃ (γ : 𝒪[L]) (P : 𝒪[K][X]), P.Monic ∧ aeval γ P = 0 ∧ IsUnit (aeval γ (derivative P)) ∧
      E = K⟮(γ : L)⟯ := by
  obtain ⟨β, P, hPm, hβ, -, hd, htop⟩ := IsUnramified.exists_generator K E
  refine ⟨algebraMap 𝒪[E] 𝒪[L] β, P, hPm, ?_, ?_, ?_⟩
  · rw [aeval_algebraMap_apply, hβ, map_zero]
  · rw [aeval_algebraMap_apply]
    exact hd.map _
  · have := congrArg (IntermediateField.map E.val) htop
    rw [IntermediateField.adjoin_map, Set.image_singleton, ← AlgHom.fieldRange_eq_map,
      IntermediateField.fieldRange_val] at this
    exact this.symm

theorem exists_maximalUnramified_eq :
    ∃ (β : 𝒪[L]) (P : 𝒪[K][X]), P.Monic ∧ aeval β P = 0 ∧ IsUnit (aeval β (derivative P)) ∧
      maximalUnramified K L = K⟮(β : L)⟯ ∧ IsUnramified K K⟮(β : L)⟯ ∧
      Module.finrank K K⟮(β : L)⟯ = residueDegree K L ∧ residueDegree K⟮(β : L)⟯ L = 1 := by
  obtain ⟨β, P, hPm, hβ, hsep, hunr, hdeg, h1⟩ := exists_unramified_adjoin K L
  refine ⟨β, P, hPm, hβ, isUnit_aeval_derivative_of_separable K L P hsep β hβ, ?_, hunr, hdeg, h1⟩
  refine le_antisymm (sSup_le fun E hE ↦ ?_) (le_sSup hunr)
  have : IsUnramified K E := hE
  obtain ⟨γ, Q, hQ, hγ, hd, hE'⟩ := exists_generator_of_isUnramified K L E
  rw [hE']
  exact IntermediateField.adjoin_simple_le_iff.2 (mem_of_residueDegree_eq_one K L _ h1 Q hQ γ hγ hd)

instance isUnramified_maximalUnramified : IsUnramified K (maximalUnramified K L) := by
  obtain ⟨β, P, -, -, -, heq, hunr, -, -⟩ := exists_maximalUnramified_eq K L
  rw [heq]
  exact hunr

theorem finrank_maximalUnramified :
    Module.finrank K (maximalUnramified K L) = residueDegree K L := by
  obtain ⟨β, P, -, -, -, heq, -, hdeg, -⟩ := exists_maximalUnramified_eq K L
  rw [heq]
  exact hdeg

theorem IsUnramified.sup (E F : IntermediateField K L) [IsUnramified K E] [IsUnramified K F] :
    IsUnramified K (E ⊔ F : IntermediateField K L) :=
  IsUnramified.of_le (sup_le (le_maximalUnramified K L E) (le_maximalUnramified K L F))

theorem IsUnramified.iSup {ι : Type*} (E : ι → IntermediateField K L)
    [∀ i, IsUnramified K (E i)] : IsUnramified K (⨆ i, E i : IntermediateField K L) :=
  IsUnramified.of_le (iSup_le fun i ↦ le_maximalUnramified K L (E i))

end Maximal

section BaseChange

variable (K K' L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field K'] [ValuativeRel K'] [TopologicalSpace K']
  [IsNonarchimedeanLocalField K'] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K K'] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
  [ValuativeExtension K K'] [ValuativeExtension K' L] [ValuativeExtension K L]
  [FiniteDimensional K L]

end BaseChange

section Galois

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

def inertiaSubgroup : Subgroup (L ≃ₐ[K] L) := (residueAlgEquiv K L).ker

theorem inertiaSubgroup_apply_eq (σ : L ≃ₐ[K] L) (hσ : σ ∈ inertiaSubgroup K L) (P : 𝒪[K][X])
    (γ : 𝒪[L]) (hγ : aeval γ P = 0) (hd : IsUnit (aeval γ (derivative P))) : σ γ = γ := by
  set γσ := integerAlgEquiv K L σ γ
  have h0 : aeval γσ P = 0 := by
    have := aeval_algHom_apply (integerAlgEquiv K L σ : 𝒪[L] →ₐ[𝒪[K]] 𝒪[L]) γ P
    rw [hγ, map_zero] at this
    exact this
  have hres : residue 𝒪[L] γσ = residue 𝒪[L] γ := by
    have h1 : residueAlgEquiv K L σ = 1 := hσ
    rw [← residueAlgEquiv_residue, h1]
    rfl
  have heq : γ = γσ := by
    refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub (f := P.map (algebraMap 𝒪[K] 𝒪[L]))
      (by rw [eval_map_algebraMap]; exact hγ) (by rw [eval_map_algebraMap]; exact h0) ?_ ?_
    · rw [← mem_nonunits_iff, ← mem_maximalIdeal, ← residue_eq_zero_iff, map_sub, hres, sub_self]
    · rw [derivative_map, eval_map_algebraMap]
      exact hd
  rw [← coe_integerAlgEquiv_apply]
  exact congrArg Subtype.val heq.symm

theorem maximalUnramified_le_fixedField :
    maximalUnramified K L ≤ IntermediateField.fixedField (inertiaSubgroup K L) := by
  obtain ⟨β, P, -, hβ, hd, heq, -, -, -⟩ := exists_maximalUnramified_eq K L
  rw [heq, IntermediateField.adjoin_simple_le_iff]
  exact fun σ ↦ inertiaSubgroup_apply_eq K L σ σ.2 P β hβ hd

variable [IsGalois K L]

theorem inertiaSubgroup_counting :
    Nat.card (inertiaSubgroup K L) = ramificationIndex K L ∧
      Nat.card (residueAlgEquiv K L).range = residueDegree K L ∧
      Module.finrank K (IntermediateField.fixedField (inertiaSubgroup K L)) = residueDegree K L := by
  set I := inertiaSubgroup K L
  set F := IntermediateField.fixedField I
  have hn := ramificationIndex_mul_residueDegree K L
  have hf := residueDegree_pos K L
  have he := ramificationIndex_pos K L
  have hFL : Module.finrank F L = Nat.card I := IntermediateField.finrank_fixedField_eq_card I
  have hG : Nat.card (L ≃ₐ[K] L) = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
  have hIdx : Nat.card I * I.index = Nat.card (L ≃ₐ[K] L) := Subgroup.card_mul_index I
  have hind : I.index = Nat.card (residueAlgEquiv K L).range := Subgroup.index_ker _
  have hrange : Nat.card (residueAlgEquiv K L).range ≤ residueDegree K L := by
    calc Nat.card (residueAlgEquiv K L).range ≤ Nat.card (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) :=
          Subgroup.card_le_card_group _
      _ = Module.finrank 𝓀[K] 𝓀[L] := IsGalois.card_aut_eq_finrank _ _
      _ = residueDegree K L := (residueDegree_eq_finrank K L).symm
  have hFK : Module.finrank K F * Module.finrank F L = Module.finrank K L :=
    Module.finrank_mul_finrank K F L
  have hTF : residueDegree K L ≤ Module.finrank K F := by
    rw [← finrank_maximalUnramified K L]
    exact IntermediateField.finrank_le_of_le_right (maximalUnramified_le_fixedField K L)
  set a := Nat.card I
  set r := Nat.card (residueAlgEquiv K L).range
  set e := ramificationIndex K L
  set f := residueDegree K L
  set d := Module.finrank K F
  rw [hind, hG, ← hn] at hIdx
  rw [hFL, ← hn] at hFK
  have h1 : a ≤ e := by
    refine Nat.le_of_mul_le_mul_left ?_ hf
    calc f * a ≤ d * a := Nat.mul_le_mul_right _ hTF
      _ = e * f := hFK
      _ = f * e := mul_comm _ _
  have h2 : e ≤ a := by
    refine Nat.le_of_mul_le_mul_right ?_ hf
    calc e * f = a * r := hIdx.symm
      _ ≤ a * f := Nat.mul_le_mul_left _ hrange
  have hae : a = e := le_antisymm h1 h2
  refine ⟨hae, ?_, ?_⟩
  · rw [hae] at hIdx
    exact (Nat.eq_of_mul_eq_mul_left he hIdx)
  · rw [hae, mul_comm e f] at hFK
    exact Nat.eq_of_mul_eq_mul_right he hFK

theorem card_inertiaSubgroup : Nat.card (inertiaSubgroup K L) = ramificationIndex K L :=
  (inertiaSubgroup_counting K L).1

end Galois

end GroundTheory.LocalField
