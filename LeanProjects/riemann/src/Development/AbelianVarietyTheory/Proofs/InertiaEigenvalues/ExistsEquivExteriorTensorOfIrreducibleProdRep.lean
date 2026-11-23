import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryAdmissibleMatrixCoefficient

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TensorFactor

variable {G H X Y : Type} [Group G] [Group H] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
  [Module ℂ Y] (τ : Representation ℂ (G × H) X) (ρ : Representation ℂ H Y)

def homSpace : Submodule ℂ (Y →ₗ[ℂ] X) where
  carrier := {φ | ∀ h v, φ (ρ h v) = τ (1, h) (φ v)}
  add_mem' := by
    intro a b ha hb h v
    simp [ha h v, hb h v]
  zero_mem' := by intro h v; simp
  smul_mem' := by
    intro c a ha h v
    simp [ha h v]

theorem commute_apply (g : G) (h : H) (x : X) : τ (g, 1) (τ (1, h) x) = τ (1, h) (τ (g, 1) x) := by
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  simp

theorem apply_pair (g : G) (h : H) (x : X) : τ (g, h) x = τ (g, 1) (τ (1, h) x) := by
  rw [← Module.End.mul_apply, ← map_mul]
  simp

def homRep : Representation ℂ G (homSpace τ ρ) where
  toFun g :=
    { toFun := fun φ => ⟨(τ (g, 1)).comp φ.1, fun h v => by
        simp only [LinearMap.comp_apply]
        rw [φ.2 h v, commute_apply]⟩
      map_add' := fun φ ψ => by ext; simp
      map_smul' := fun c φ => by ext; simp }
  map_one' := by
    ext φ v
    have : ((1 : G), (1 : H)) = (1 : G × H) := rfl
    simp [this]
  map_mul' a b := by
    ext φ v
    have : ((a * b, (1 : H)) : G × H) = (a, 1) * (b, 1) := by simp
    show τ (a * b, 1) _ = τ (a, 1) (τ (b, 1) _)
    rw [this, map_mul, Module.End.mul_apply]

@[simp] theorem homRep_apply_coe (g : G) (φ : homSpace τ ρ) :
    ((homRep τ ρ g φ : homSpace τ ρ) : Y →ₗ[ℂ] X) = (τ (g, 1)).comp (φ : Y →ₗ[ℂ] X) := rfl

def evMap : (extTensor (homRep τ ρ) ρ).IntertwiningMap τ where
  toLinearMap := TensorProduct.lift (homSpace τ ρ).subtype
  isIntertwining' gh := by
    apply TensorProduct.ext'
    intro φ v
    obtain ⟨g, h⟩ := gh
    simp only [LinearMap.comp_apply, extTensor_tmul, TensorProduct.lift.tmul, Submodule.subtype_apply,
      homRep_apply_coe]
    rw [φ.2 h v, ← apply_pair]

@[simp] theorem evMap_tmul (φ : homSpace τ ρ) (v : Y) :
    evMap τ ρ (φ ⊗ₜ v) = (φ : Y →ₗ[ℂ] X) v := rfl

end GlobalTheory.TensorFactor

namespace GlobalTheory.TensorFactor

variable {G H X Y : Type} [Group G] [Group H] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
  [Module ℂ Y] (τ : Representation ℂ (G × H) X) (ρ : Representation ℂ H Y)

def diffMap (g : G) (φ : homSpace τ ρ) :
    ρ.IntertwiningMap (τ.comp (MonoidHom.inr G H)) where
  toLinearMap := (τ (g, 1)).comp (φ : Y →ₗ[ℂ] X) - (φ : Y →ₗ[ℂ] X)
  isIntertwining' h := by
    ext v
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, MonoidHom.coe_comp, Function.comp_apply,
      MonoidHom.inr_apply, map_sub]
    rw [φ.2 h v, commute_apply]

theorem homRep_eq_of_apply_eq [ρ.IsIrreducible] {g : G} {φ : homSpace τ ρ} {y : Y} (hy : y ≠ 0)
    (h : τ (g, 1) ((φ : Y →ₗ[ℂ] X) y) = (φ : Y →ₗ[ℂ] X) y) : homRep τ ρ g φ = φ := by
  rcases Representation.IsIrreducible.injective_or_eq_zero (diffMap τ ρ g φ) with hi | h0
  · refine absurd (hi (a₁ := y) (a₂ := 0) ?_) hy
    simp [diffMap, h]
  · apply Subtype.ext
    ext v
    have := congrArg (fun f => f v) h0
    simpa [diffMap, sub_eq_zero] using this

end GlobalTheory.TensorFactor

open GlobalTheory.TensorFactor in

theorem GlobalTheory.TensorFactor.exists_equiv_extTensor : ∀ (G H X Y : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ (G × H) X) (ρ : Representation ℂ H Y), IsSmooth τ → τ.IsIrreducible → ρ.IsIrreducible → (∀ (M : Submodule ℂ (Y →ₗ[ℂ] X)), (∀ φ ∈ M, ∀ g v, φ (ρ g v) = τ (1, g) (φ v)) → Function.Injective (TensorProduct.lift M.subtype)) → (∃ ι : Y →ₗ[ℂ] X, ι ≠ 0 ∧ ∀ g v, ι (ρ g v) = τ (1, g) (ι v)) → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (σ : Representation ℂ G W), IsSmooth σ ∧ σ.IsIrreducible ∧ Nonempty (τ.Equiv (extTensor σ ρ)) := by
  intro G H X Y _ _ _ _ _ _ _ _ _ _ τ ρ hτs hτ hρ hinj hex
  obtain ⟨ι, hι0, hι⟩ := hex
  haveI := hτ
  haveI := hρ
  have hev : Function.Injective (evMap τ ρ) := hinj (homSpace τ ρ) fun φ hφ => hφ
  let ι' : homSpace τ ρ := ⟨ι, hι⟩
  obtain ⟨y0, hy0⟩ : ∃ v, ι v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hι0 (LinearMap.ext h)
  have hy0' : y0 ≠ 0 := fun h => hy0 (by simp [h])
  have hsurj : Function.Surjective (evMap τ ρ) :=
    (Representation.IsIrreducible.surjective_or_eq_zero (evMap τ ρ)).resolve_right fun h0 =>
      hy0 (by simpa [ι'] using congrArg (fun f => f (ι' ⊗ₜ y0)) h0)
  refine ⟨homSpace τ ρ, inferInstance, inferInstance, homRep τ ρ, ?_, ?_,
    ⟨(Representation.IntertwiningMap.ofBijective (evMap τ ρ) ⟨hev, hsurj⟩).symm⟩⟩
  · refine isSmooth_of_nhds fun φ => ?_
    have hc : Continuous fun g : G => ((g, (1 : H)) : G × H) := by fun_prop
    refine Filter.mem_of_superset (((hτs ((φ : Y →ₗ[ℂ] X) y0)).preimage hc).mem_nhds ?_)
      fun g hg => homRep_eq_of_apply_eq τ ρ hy0' hg
    have : ((1 : G), (1 : H)) = (1 : G × H) := rfl
    show τ ((1 : G), (1 : H)) _ = _
    simp [this]
  · haveI : Nontrivial (Subrepresentation (homRep τ ρ)) := ⟨⊥, ⊤, fun h => by
      have h1 : ι' ∈ (⊤ : Subrepresentation (homRep τ ρ)).toSubmodule := Submodule.mem_top
      rw [← h] at h1
      have h2 : ι' = 0 := (Submodule.mem_bot ℂ).1 h1
      exact hι0 (congrArg Subtype.val h2)⟩
    refine ⟨fun S => ?_⟩
    let U : Subrepresentation τ :=
      { toSubmodule :=
          LinearMap.range ((evMap τ ρ).toLinearMap ∘ₗ LinearMap.rTensor Y S.toSubmodule.subtype)
        apply_mem_toSubmodule := by
          rintro ⟨g, h⟩ _ ⟨t, rfl⟩
          induction t using TensorProduct.induction_on with
          | zero => simp
          | tmul ψ z =>
            refine ⟨⟨homRep τ ρ g ψ, S.apply_mem_toSubmodule g ψ.2⟩ ⊗ₜ ρ h z, ?_⟩
            show ((homRep τ ρ g ψ : homSpace τ ρ) : Y →ₗ[ℂ] X) (ρ h z) =
              τ (g, h) (((ψ : homSpace τ ρ) : Y →ₗ[ℂ] X) z)
            rw [homRep_apply_coe, LinearMap.comp_apply, (ψ : homSpace τ ρ).2 h z, ← apply_pair]
          | add a b ha hb =>
            rw [map_add, map_add]
            exact add_mem ha hb }
    rcases IsSimpleOrder.eq_bot_or_eq_top U with hU | hU
    · left
      apply Subrepresentation.toSubmodule_injective
      refine eq_bot_iff.2 fun ψ hψ => (Submodule.mem_bot ℂ).2 (Subtype.ext (LinearMap.ext fun z => ?_))
      have hm : (evMap τ ρ).toLinearMap (LinearMap.rTensor Y S.toSubmodule.subtype (⟨ψ, hψ⟩ ⊗ₜ z)) ∈
          U.toSubmodule := ⟨⟨ψ, hψ⟩ ⊗ₜ z, rfl⟩
      rw [hU] at hm
      have h2 := (Submodule.mem_bot ℂ).1 hm
      have h3 : ((ψ : homSpace τ ρ) : Y →ₗ[ℂ] X) z = 0 := by simpa using h2
      simpa using h3
    · right
      apply Subrepresentation.toSubmodule_injective
      refine eq_top_iff.2 fun φ _ => ?_
      obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hy0'
      let P : homSpace τ ρ ⊗[ℂ] Y →ₗ[ℂ] homSpace τ ρ :=
        (TensorProduct.rid ℂ (homSpace τ ρ)).toLinearMap ∘ₗ LinearMap.lTensor (homSpace τ ρ) l
      have hP : ∀ t, P (LinearMap.rTensor Y S.toSubmodule.subtype t) ∈ S.toSubmodule := by
        intro t
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul ψ z => simpa [P] using S.toSubmodule.smul_mem (l z) ψ.2
        | add a b ha hb =>
          rw [map_add, map_add]
          exact add_mem ha hb
      have hmem : evMap τ ρ (φ ⊗ₜ y0) ∈ U.toSubmodule := by
        rw [hU]
        exact Submodule.mem_top
      obtain ⟨t, ht⟩ := hmem
      have ht' : LinearMap.rTensor Y S.toSubmodule.subtype t = φ ⊗ₜ y0 :=
        hev (a₁ := LinearMap.rTensor Y S.toSubmodule.subtype t) (a₂ := φ ⊗ₜ y0) ht
      have := hP t
      rw [ht'] at this
      simpa [P, hl] using this
