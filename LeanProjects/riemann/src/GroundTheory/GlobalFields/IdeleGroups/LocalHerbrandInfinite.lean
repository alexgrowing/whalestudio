import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.LocalHerbrand
import GroundTheory.GlobalFields.InfiniteNormIndex.LocalSymbol

noncomputable section

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion GroundTheory.GroupCoh

open scoped NumberField.LiesOver

namespace GroundTheory.Global

section NeZero

variable {k G V : Type*} [CommRing k] [Group G] [Fintype G] [AddCommGroup V] [Module k V]

theorem hasHerbrandQuotient_of_cycHerbrand_ne_zero {ρ : Representation k G V} {σ : G}
    (h : cycHerbrand ρ σ ≠ 0) : HasHerbrandQuotient (cycSubOne ρ σ) (cycNorm ρ) := by
  rw [cycHerbrand_eq] at h
  have h0 : Nat.card (CycTateZero ρ σ) ≠ 0 := fun h' ↦ h (by rw [h', Nat.cast_zero, zero_div])
  have h1 : Nat.card (CycTateNegOne ρ σ) ≠ 0 := fun h' ↦ h (by rw [h', Nat.cast_zero, div_zero])
  exact ⟨Nat.finite_of_card_ne_zero h0, Nat.finite_of_card_ne_zero h1⟩

end NeZero

section Action

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (w : InfinitePlace L)

theorem apply_algEquiv_of_mem_stabilizer {σ : Gal(L/K)}
    (hσ : σ ∈ MulAction.stabilizer Gal(L/K) w) (x : L) : w (σ x) = w x := by
  have h := congrArg (fun u : InfinitePlace L ↦ u (σ x)) (MulAction.mem_stabilizer_iff.1 hσ)
  simp only [InfinitePlace.smul_apply, AlgEquiv.symm_apply_apply] at h
  exact h.symm

def withAbsMapOf (σ : Gal(L/K)) : WithAbs w.1 →+* WithAbs w.1 :=
  WithAbs.map w.1 w.1 (σ : L →+* L)

theorem ofAbs_withAbsMapOf (σ : Gal(L/K)) (x : WithAbs w.1) :
    (withAbsMapOf w σ x).ofAbs = σ x.ofAbs :=
  rfl

variable {w}

theorem isometry_withAbsMapOf {σ : Gal(L/K)} (hσ : σ ∈ MulAction.stabilizer Gal(L/K) w) :
    Isometry (withAbsMapOf w σ) :=
  AddMonoidHomClass.isometry_of_norm _ fun x ↦ by
    rw [WithAbs.norm_eq_apply_ofAbs, WithAbs.norm_eq_apply_ofAbs, ofAbs_withAbsMapOf]
    exact apply_algEquiv_of_mem_stabilizer w hσ x.ofAbs

def completionRingHomOf {σ : Gal(L/K)} (hσ : σ ∈ MulAction.stabilizer Gal(L/K) w) :
    w.Completion →+* w.Completion :=
  ((Completion.equiv w).symm.toRingHom.comp (isometry_withAbsMapOf hσ).mapRingHom).comp
    (Completion.equiv w).toRingHom

theorem continuous_completionRingHomOf {σ : Gal(L/K)}
    (hσ : σ ∈ MulAction.stabilizer Gal(L/K) w) : Continuous (completionRingHomOf hσ) :=
  (continuous_ofCompletion w).comp <|
    UniformSpace.Completion.continuous_map.comp (continuous_toCompletion w)

theorem completionRingHomOf_coe {σ : Gal(L/K)} (hσ : σ ∈ MulAction.stabilizer Gal(L/K) w)
    (x : WithAbs w.1) :
    completionRingHomOf hσ (x : w.Completion) = ((withAbsMapOf w σ x : WithAbs w.1) :
      w.Completion) :=
  Completion.ext <| (isometry_withAbsMapOf hσ).mapRingHom_coe x

variable (w) in

theorem ringHom_ext_completion {f g : w.Completion →+* w.Completion} (hf : Continuous f)
    (hg : Continuous g) (h : ∀ x : WithAbs w.1, f (x : w.Completion) = g (x : w.Completion)) :
    f = g :=
  RingHom.ext (congrFun ((denseRange_coe w).equalizer hf hg (funext h)))

variable (w)

instance infiniteDecompositionMulSemiringAction :
    MulSemiringAction (MulAction.stabilizer Gal(L/K) w) w.Completion where
  smul σ x := completionRingHomOf σ.2 x
  one_smul x := by
    change completionRingHomOf (1 : MulAction.stabilizer Gal(L/K) w).2 x = RingHom.id _ x
    congr 1
    exact ringHom_ext_completion w (continuous_completionRingHomOf _) continuous_id fun y ↦ by
      rw [completionRingHomOf_coe]
      rfl
  mul_smul σ τ x := by
    change completionRingHomOf (σ * τ).2 x =
      ((completionRingHomOf σ.2).comp (completionRingHomOf τ.2)) x
    congr 1
    exact ringHom_ext_completion w (continuous_completionRingHomOf _)
      ((continuous_completionRingHomOf σ.2).comp (continuous_completionRingHomOf τ.2)) fun y ↦ by
        rw [RingHom.comp_apply, completionRingHomOf_coe, completionRingHomOf_coe,
          completionRingHomOf_coe]
        rfl
  smul_zero σ := map_zero _
  smul_add σ := map_add _
  smul_one σ := map_one _
  smul_mul σ := map_mul _

instance infiniteDecompositionUnitsAction :
    MulDistribMulAction (MulAction.stabilizer Gal(L/K) w) w.Completionˣ :=
  Units.mulDistribMulActionRight

variable {w}

theorem infiniteDecomposition_smul_def (σ : MulAction.stabilizer Gal(L/K) w) (x : w.Completion) :
    σ • x = completionRingHomOf σ.2 x :=
  rfl

theorem infiniteDecomposition_smul_coe (σ : MulAction.stabilizer Gal(L/K) w) (x : WithAbs w.1) :
    σ • (x : w.Completion) =
      ((withAbsMapOf w (σ : Gal(L/K)) x : WithAbs w.1) : w.Completion) :=
  completionRingHomOf_coe σ.2 x

theorem continuous_infiniteDecomposition_smul (σ : MulAction.stabilizer Gal(L/K) w) :
    Continuous fun x : w.Completion ↦ σ • x :=
  continuous_completionRingHomOf σ.2

end Action

section Local

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (v : InfinitePlace K)
  (w : InfinitePlace L) [w.LiesOver v]

theorem infiniteDecomposition_smul_algebraMap (σ : MulAction.stabilizer Gal(L/K) w)
    (c : v.Completion) :
    σ • algebraMap v.Completion w.Completion c = algebraMap v.Completion w.Completion c := by
  have h := (denseRange_coe v).equalizer
    ((continuous_infiniteDecomposition_smul σ).comp
      (continuous_algebraMap v.Completion w.Completion))
    (continuous_algebraMap v.Completion w.Completion) (funext fun x ↦ ?_)
  · exact congrFun h c
  · simp only [Function.comp_apply]
    rw [Completion.algebraMap_coe, infiniteDecomposition_smul_coe]
    congr 2
    apply (WithAbs.equiv w.1).injective
    change σ.1 (algebraMap (WithAbs v.1) (WithAbs w.1) x).ofAbs =
      (algebraMap (WithAbs v.1) (WithAbs w.1) x).ofAbs
    rw [WithAbs.ofAbs_algebraMap, AlgEquiv.commutes]

def infiniteDecompositionAlgEquiv (σ : MulAction.stabilizer Gal(L/K) w) :
    Gal(w.Completion/v.Completion) :=
  AlgEquiv.ofRingEquiv (f := MulSemiringAction.toRingEquiv _ w.Completion σ)
    (infiniteDecomposition_smul_algebraMap v w σ)

@[simp]
theorem infiniteDecompositionAlgEquiv_apply (σ : MulAction.stabilizer Gal(L/K) w)
    (x : w.Completion) : infiniteDecompositionAlgEquiv v w σ x = σ • x :=
  rfl

def infiniteDecompositionToLocal :
    MulAction.stabilizer Gal(L/K) w →* Gal(w.Completion/v.Completion) where
  toFun := infiniteDecompositionAlgEquiv v w
  map_one' := AlgEquiv.ext fun x ↦ one_smul (MulAction.stabilizer Gal(L/K) w) x
  map_mul' σ τ := AlgEquiv.ext fun x ↦ mul_smul σ τ x

@[simp]
theorem infiniteDecompositionToLocal_apply (σ : MulAction.stabilizer Gal(L/K) w)
    (x : w.Completion) : infiniteDecompositionToLocal v w σ x = σ • x :=
  rfl

theorem infiniteDecompositionToLocal_injective :
    Function.Injective (infiniteDecompositionToLocal v w) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  have h := congrArg (fun f : Gal(w.Completion/v.Completion) ↦
    f ((WithAbs.toAbs w.1 x : WithAbs w.1) : w.Completion)) hσ
  simp only [AlgEquiv.one_apply] at h
  rw [infiniteDecompositionToLocal_apply, infiniteDecomposition_smul_coe] at h
  have h' := UniformSpace.Completion.coe_injective (WithAbs w.1)
    (congrArg Completion.toCompletion h)
  rw [OneMemClass.coe_one, AlgEquiv.one_apply]
  exact congrArg WithAbs.ofAbs h'

variable [IsGalois K L]

theorem natCard_infiniteDecompositionGroup :
    Nat.card (MulAction.stabilizer Gal(L/K) w) = Module.finrank v.Completion w.Completion := by
  rw [NumberField.InfinitePlace.card_stabilizer]
  by_cases h : w.IsUnramified K
  · rw [if_pos h, h.finrank_eq_one v]
  · rw [if_neg h, NumberField.InfinitePlace.IsRamified.finrank_eq_two v h]

theorem infiniteDecompositionToLocal_bijective :
    Function.Bijective (infiniteDecompositionToLocal v w) := by
  refine (infiniteDecompositionToLocal_injective v w).bijective_of_nat_card_le ?_
  rw [natCard_infiniteDecompositionGroup v w, InfinitePlace.natCard_gal_completion w]

def infiniteDecompositionMulEquiv :
    MulAction.stabilizer Gal(L/K) w ≃* Gal(w.Completion/v.Completion) :=
  MulEquiv.ofBijective (infiniteDecompositionToLocal v w)
    (infiniteDecompositionToLocal_bijective v w)

@[simp]
theorem infiniteDecompositionMulEquiv_apply (σ : MulAction.stabilizer Gal(L/K) w)
    (x : w.Completion) : infiniteDecompositionMulEquiv v w σ x = σ • x :=
  rfl

end Local

section Herbrand

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (v : InfinitePlace K)
  (w : InfinitePlace L) [w.LiesOver v]

theorem ofMulDistribMulAction_gal_completion_units (σ : Gal(w.Completion/v.Completion))
    (x : Additive w.Completionˣ) :
    Representation.ofMulDistribMulAction Gal(w.Completion/v.Completion) w.Completionˣ σ x =
      InfinitePlace.unitsRep v w σ x := by
  apply Additive.toMul.injective
  apply Units.ext
  rfl

theorem cycHerbrand_gal_completion_units (σ : Gal(w.Completion/v.Completion))
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    HasHerbrandQuotient
        (cycSubOne (Representation.ofMulDistribMulAction Gal(w.Completion/v.Completion)
          w.Completionˣ) σ)
        (cycNorm (Representation.ofMulDistribMulAction Gal(w.Completion/v.Completion)
          w.Completionˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction Gal(w.Completion/v.Completion)
          w.Completionˣ) σ = Module.finrank v.Completion w.Completion := by
  have h1 := (cycHerbrand_eq_of_mulEquiv
    (ρ' := Representation.ofMulDistribMulAction Gal(w.Completion/v.Completion) w.Completionˣ)
    (ρ := InfinitePlace.unitsRep v w) (MulEquiv.refl _) (AddEquiv.refl _)
    (fun g x ↦ ofMulDistribMulAction_gal_completion_units v w g x) σ).2
  have h2 : cycHerbrand (InfinitePlace.unitsRep v w) σ = Module.finrank v.Completion w.Completion :=
    InfinitePlace.cyclicHerbrand_unitsRep_eq_finrank v w σ hσ
  have h3 : cycHerbrand (Representation.ofMulDistribMulAction Gal(w.Completion/v.Completion)
      w.Completionˣ) σ = Module.finrank v.Completion w.Completion := h1.trans h2
  refine ⟨hasHerbrandQuotient_of_cycHerbrand_ne_zero ?_, h3⟩
  rw [h3, Nat.cast_ne_zero]
  exact Module.finrank_pos.ne'

variable [IsGalois K L]

theorem ofMulDistribMulAction_infiniteDecomposition_units
    (σ : MulAction.stabilizer Gal(L/K) w) (x : Additive w.Completionˣ) :
    Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w) w.Completionˣ σ x =
      Representation.ofMulDistribMulAction Gal(w.Completion/v.Completion) w.Completionˣ
        (infiniteDecompositionMulEquiv v w σ) x := by
  apply Additive.toMul.injective
  apply Units.ext
  rfl

theorem cycHerbrand_infiniteCompletion_units [Fintype (MulAction.stabilizer Gal(L/K) w)]
    (τ : MulAction.stabilizer Gal(L/K) w) (hτ : ∀ σ, σ ∈ Subgroup.zpowers τ) :
    HasHerbrandQuotient
        (cycSubOne (Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w)
          w.Completionˣ) τ)
        (cycNorm (Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w)
          w.Completionˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w)
          w.Completionˣ) τ = Module.finrank v.Completion w.Completion := by
  obtain ⟨h1, h2⟩ := cycHerbrand_eq_of_mulEquiv
    (ρ' := Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w) w.Completionˣ)
    (ρ := Representation.ofMulDistribMulAction Gal(w.Completion/v.Completion) w.Completionˣ)
    (infiniteDecompositionMulEquiv v w) (AddEquiv.refl _)
    (fun σ x ↦ ofMulDistribMulAction_infiniteDecomposition_units v w σ x) τ
  obtain ⟨h3, h4⟩ := cycHerbrand_gal_completion_units v w _
    (mem_zpowers_mulEquiv (infiniteDecompositionMulEquiv v w) hτ)
  exact ⟨h1.2 h3, h2.trans h4⟩

end Herbrand

end GroundTheory.Global
