import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.SplitA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.DerivExistsAllPosStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.HasDerivAtRealOfComplex
import Mathlib.Analysis.InnerProductSpace.TensorProduct

noncomputable section

open Matrix Finset TensorProduct

namespace ReciprocityTheory.ChartRestriction.TR.Weyl

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HW

section Tens

variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

theorem sp_mapL_one : mapL (1 : E →L[ℂ] E) (1 : F →L[ℂ] F) = 1 := mapL_id_id

theorem sp_star_mapL (A : E →L[ℂ] E) (B : F →L[ℂ] F) : star (mapL A B) = mapL (star A) (star B) := by
  have := FiniteDimensional.complete ℂ E
  have := FiniteDimensional.complete ℂ F
  have := FiniteDimensional.complete ℂ (E ⊗[ℂ] F)
  simp only [ContinuousLinearMap.star_eq_adjoint, adjoint_mapL]

theorem sp_mapL_unitary (A : unitary (E →L[ℂ] E)) (B : unitary (F →L[ℂ] F)) :
    mapL (A : E →L[ℂ] E) (B : F →L[ℂ] F) ∈ unitary (E ⊗[ℂ] F →L[ℂ] E ⊗[ℂ] F) := by
  rw [Unitary.mem_iff, sp_star_mapL, ← mapL_mul, ← mapL_mul, Unitary.star_mul_self_of_mem A.2,
    Unitary.star_mul_self_of_mem B.2, Unitary.mul_star_self_of_mem A.2, Unitary.mul_star_self_of_mem B.2]
  exact ⟨sp_mapL_one, sp_mapL_one⟩

def sp_tensU {G : Type*} [Monoid G] (ρ1 : G →* unitary (E →L[ℂ] E)) (ρ2 : G →* unitary (F →L[ℂ] F)) :
    G →* unitary (E ⊗[ℂ] F →L[ℂ] E ⊗[ℂ] F) where
  toFun g := ⟨mapL (ρ1 g : E →L[ℂ] E) (ρ2 g : F →L[ℂ] F), sp_mapL_unitary _ _⟩
  map_one' := Subtype.ext (by
    show mapL _ _ = 1
    rw [map_one, map_one]
    exact sp_mapL_one)
  map_mul' g h := Subtype.ext (by
    show mapL _ _ = mapL _ _ * mapL _ _
    rw [map_mul, map_mul]
    exact mapL_mul _ _ _ _)

def tensorLeftOperator : (E →L[ℂ] E) →L[ℂ] (E ⊗[ℂ] F →L[ℂ] E ⊗[ℂ] F) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => mapL A (1 : F →L[ℂ] F)
      map_add' := fun _ _ => mapL_add_left _ _ _
      map_smul' := fun _ _ => mapL_smul_left _ _ _ }

def tensorRightOperator : (F →L[ℂ] F) →L[ℂ] (E ⊗[ℂ] F →L[ℂ] E ⊗[ℂ] F) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun B => mapL (1 : E →L[ℂ] E) B
      map_add' := fun _ _ => mapL_add_right _ _ _
      map_smul' := fun _ _ => mapL_smul_right _ _ _ }

theorem tensorLeftOperator_apply (A : E →L[ℂ] E) : (tensorLeftOperator : _ →L[ℂ] (E ⊗[ℂ] F →L[ℂ] E ⊗[ℂ] F)) A =
    mapL A (1 : F →L[ℂ] F) := rfl

theorem tensorRightOperator_apply (B : F →L[ℂ] F) : (tensorRightOperator : _ →L[ℂ] (E ⊗[ℂ] F →L[ℂ] E ⊗[ℂ] F)) B =
    mapL (1 : E →L[ℂ] E) B := rfl

theorem sp_mapL_split (A : E →L[ℂ] E) (B : F →L[ℂ] F) :
    mapL A B = mapL A (1 : F →L[ℂ] F) * mapL (1 : E →L[ℂ] E) B := by
  rw [← mapL_mul, mul_one, one_mul]

theorem sp_tensU_cont {G : Type*} [Monoid G] [TopologicalSpace G] (ρ1 : G →* unitary (E →L[ℂ] E))
    (ρ2 : G →* unitary (F →L[ℂ] F)) (h1 : Continuous ρ1) (h2 : Continuous ρ2) :
    Continuous (sp_tensU ρ1 ρ2) := by
  have c1 : Continuous fun g => (ρ1 g : E →L[ℂ] E) := continuous_subtype_val.comp h1
  have c2 : Continuous fun g => (ρ2 g : F →L[ℂ] F) := continuous_subtype_val.comp h2
  have h : Continuous fun g => mapL (ρ1 g : E →L[ℂ] E) (ρ2 g : F →L[ℂ] F) := by
    have e : (fun g => mapL (ρ1 g : E →L[ℂ] E) (ρ2 g : F →L[ℂ] F)) =
        fun g => mapL (ρ1 g : E →L[ℂ] E) (1 : F →L[ℂ] F) * mapL (1 : E →L[ℂ] E) (ρ2 g : F →L[ℂ] F) :=
      funext fun g => sp_mapL_split _ _
    rw [e]
    exact ((tensorLeftOperator (F := F)).continuous.comp c1).mul ((tensorRightOperator (E := E)).continuous.comp c2)
  exact Continuous.subtype_mk h _

theorem sp_mapL_hasDeriv {a : ℝ → E →L[ℂ] E} {b : ℝ → F →L[ℂ] F} {a' : E →L[ℂ] E} {b' : F →L[ℂ] F}
    (ha : HasDerivAt a a' 0) (hb : HasDerivAt b b' 0) (ha0 : a 0 = 1) (hb0 : b 0 = 1) :
    HasDerivAt (fun t => mapL (a t) (b t)) (mapL a' (1 : F →L[ℂ] F) + mapL (1 : E →L[ℂ] E) b') 0 := by
  have h1 := ((tensorLeftOperator (F := F)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) ha
  have h2 := ((tensorRightOperator (E := E)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hb
  have h := h1.mul h2
  simp only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars', tensorLeftOperator_apply, tensorRightOperator_apply,
    ha0, hb0, sp_mapL_one, mul_one, one_mul] at h
  have e : (fun t => mapL (a t) (b t)) = fun t => mapL (a t) (1 : F →L[ℂ] F) * mapL (1 : E →L[ℂ] E) (b t) :=
    funext fun t => sp_mapL_split _ _
  rw [e]
  exact h

end Tens

variable {n : ℕ} {ε : Fin n → Bool} {Λ1 : Fin (cnt ε true) → ℝ} {Λ2 : Fin (cnt ε false) → ℝ}

theorem sp_sub_add (ε : Fin n → Bool) (c : Bool) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    sp_sub ε c (X + Y) = sp_sub ε c X + sp_sub ε c Y := by
  ext; simp [sp_sub]

def sp_dτ (T1 : KType (fun _ : Fin (cnt ε true) => true) Λ1)
    (T2 : KType (fun _ : Fin (cnt ε false) => true) Λ2) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (T1.V ⊗[ℂ] T2.V →L[ℂ] T1.V ⊗[ℂ] T2.V) where
  toFun X := mapL (T1.dτ (sp_sub ε true X)) 1 + mapL 1 (T2.dτ (sp_sub ε false X))
  map_add' X Y := by
    simp only [sp_sub_add, map_add, mapL_add_left, mapL_add_right]
    abel
  map_smul' c X := by
    simp only [sp_sub_smul, map_smul, mapL_smul_left, mapL_smul_right, smul_add, RingHom.id_apply]

theorem sp_dτ_apply (T1 : KType (fun _ : Fin (cnt ε true) => true) Λ1)
    (T2 : KType (fun _ : Fin (cnt ε false) => true) Λ2) (X : Matrix (Fin n) (Fin n) ℂ) :
    sp_dτ T1 T2 X = mapL (T1.dτ (sp_sub ε true X)) 1 + mapL 1 (T2.dτ (sp_sub ε false X)) := rfl

theorem sp_curve_zero {X : Matrix (Fin n) (Fin n) ℂ} {γ : ℝ → KG ε}
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) : γ 0 = 1 :=
  onep_KG_ext (by rw [hγ 0]; simp; rfl)

def sp_rep (T1 : KType (fun _ : Fin (cnt ε true) => true) Λ1)
    (T2 : KType (fun _ : Fin (cnt ε false) => true) Λ2) : KRep ε where
  V := T1.V ⊗[ℂ] T2.V
  instCS := FiniteDimensional.complete ℂ _
  τ := sp_tensU (T1.τ.comp (sp_proj ε true)) (T2.τ.comp (sp_proj ε false))
  cont := sp_tensU_cont _ _ (T1.cont.comp (sp_proj_cont ε true)) (T2.cont.comp (sp_proj_cont ε false))
  dτ := sp_dτ T1 T2
  hasDeriv := by
    intro X hX γ hγ
    have h1 := T1.hasDeriv _ (sp_sub_inK true hX) (fun t => sp_proj ε true (γ t))
      (sp_proj_curve true hX hγ)
    have h2 := T2.hasDeriv _ (sp_sub_inK false hX) (fun t => sp_proj ε false (γ t))
      (sp_proj_curve false hX hγ)
    have e0 := sp_curve_zero hγ
    refine sp_mapL_hasDeriv h1 h2 ?_ ?_
    · simp only [e0, map_one]; rfl
    · simp only [e0, map_one]; rfl

theorem sp_rep_op (T1 : KType (fun _ : Fin (cnt ε true) => true) Λ1)
    (T2 : KType (fun _ : Fin (cnt ε false) => true) Λ2) (k : KG ε) :
    (sp_rep T1 T2).op k = mapL (T1.op (sp_proj ε true k)) (T2.op (sp_proj ε false k)) := rfl

theorem sp_units_true (T1 : KType (fun _ : Fin (cnt ε true) => true) Λ1)
    (T2 : KType (fun _ : Fin (cnt ε false) => true) Λ2) (r s : Fin (cnt ε true))
    (x : T1.V ⊗[ℂ] T2.V) :
    (sp_rep T1 T2).units (blk ε true r) (blk ε true s) x = TensorProduct.map (kunits T1 r s) LinearMap.id x := by
  show (sp_dτ T1 T2 (single (blk ε true r) (blk ε true s) 1)) x = _
  simp [sp_dτ_apply, sp_sub_single_same, sp_sub_single_other, kunits, mapL_apply]
  rfl

theorem sp_units_false (T1 : KType (fun _ : Fin (cnt ε true) => true) Λ1)
    (T2 : KType (fun _ : Fin (cnt ε false) => true) Λ2) (r s : Fin (cnt ε false))
    (x : T1.V ⊗[ℂ] T2.V) :
    (sp_rep T1 T2).units (blk ε false r) (blk ε false s) x = TensorProduct.map LinearMap.id (kunits T2 r s) x := by
  show (sp_dτ T1 T2 (single (blk ε false r) (blk ε false s) 1)) x = _
  simp [sp_dτ_apply, sp_sub_single_same, sp_sub_single_other, kunits, mapL_apply]
  rfl

end ReciprocityTheory.ChartRestriction.TR.Weyl
