import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.AlgebraicityClass

open NumberField Module WeierstrassCurve IntermediateField
open scoped nonZeroDivisors

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

section Extend

variable {K : Type*} [Field K] [Algebra K ℂ]

theorem exists_algEquiv_extend_adjoin {α : ℂ} (hα : IsAlgebraic K α) (φ : K⟮α⟯ →ₐ[K] ℂ) :
    ∃ σ : ℂ ≃ₐ[K] ℂ, ∀ z : K⟮α⟯, σ z = φ z := by
  have hint := hα.isIntegral
  have hroot : Polynomial.aeval (φ (AdjoinSimple.gen K α)) (minpoly K α) = 0 := by
    rw [Polynomial.aeval_algHom_apply, aeval_gen_minpoly, map_zero]
  have heq : minpoly K α = minpoly K (φ (AdjoinSimple.gen K α)) :=
    minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hroot (minpoly.monic hint)
  obtain ⟨σ, hσ⟩ := exists_algEquiv_apply_eq_of_minpoly_eq hα heq
  refine ⟨σ, fun z ↦ ?_⟩
  have e : (σ.toAlgHom.comp (K⟮α⟯).val) = φ := by
    apply adjoin_algHom_ext
    rintro x rfl
    exact hσ
  exact DFunLike.congr_fun e z

end Extend

variable {K : Type*} [Field K] [NumberField K] [Algebra K ℂ] (hK : finrank ℚ K = 2)
  [IsTotallyComplex K]
include hK

def galClassHom : (ℂ ≃ₐ[K] ℂ) →* ClassGroup (𝓞 K) where
  toFun σ := galClass (algebraMap K ℂ) hK σ.toRingEquiv
  map_one' := galClass_one (algebraMap K ℂ) hK
  map_mul' σ τ := galClass_mul (algebraMap K ℂ) hK σ.toRingEquiv τ.toRingEquiv
    (fun k ↦ σ.commutes k) (fun k ↦ τ.commutes k)

theorem galClassHom_apply_j (σ : ℂ ≃ₐ[K] ℂ) (x : ELL K) :
    σ (ELL.j x) = ELL.j ((ellMulAction (algebraMap K ℂ) hK).smul (galClassHom hK σ) x) :=
  apply_j_eq_j_galClass_smul (algebraMap K ℂ) hK σ.toRingEquiv (fun k ↦ σ.commutes k) x

theorem galClassHom_eq_one_iff (σ : ℂ ≃ₐ[K] ℂ) (x : ELL K) :
    galClassHom hK σ = 1 ↔ σ (ELL.j x) = ELL.j x :=
  galClass_eq_one_iff (algebraMap K ℂ) hK σ.toRingEquiv (fun k ↦ σ.commutes k) x

theorem ELL.isAlgebraic_j_over (x : ELL K) : IsAlgebraic K (ELL.j x) := by
  have : IsScalarTower ℚ K ℂ := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  exact IsAlgebraic.extendScalars (algebraMap ℚ K).injective (ELL.isAlgebraic_j hK x)

theorem ELL.j_mem_adjoin (x y : ELL K) : ELL.j y ∈ K⟮ELL.j x⟯ := by
  have key : ∀ ρ : ℂ ≃ₐ[K⟮ELL.j x⟯] ℂ, ρ (ELL.j y) = ELL.j y := by
    intro ρ
    have h1 : (ρ.restrictScalars K) (ELL.j x) = ELL.j x :=
      ρ.commutes (AdjoinSimple.gen K (ELL.j x))
    rw [← galClassHom_eq_one_iff hK] at h1
    have h2 := galClassHom_apply_j hK (ρ.restrictScalars K) y
    rw [h1, ellMulAction_one_smul] at h2
    exact h2
  obtain ⟨w, hw⟩ := IntermediateField.mem_bot.1
    ((mem_bot_iff_forall_algEquiv_apply_eq (F := K⟮ELL.j x⟯)).2 key)
  rw [← hw]
  exact w.2

section Field

variable (M : IntermediateField K ℂ) (hM : ∀ y : ELL K, ELL.j y ∈ M)
include hM

omit [NumberField K] hK [IsTotallyComplex K] in
theorem adjoin_j_le (x : ELL K) : K⟮ELL.j x⟯ ≤ M :=
  adjoin_simple_le_iff.2 (hM x)

def extendOf (τ : M ≃ₐ[K] M) : ℂ ≃ₐ[K] ℂ :=
  (exists_algEquiv_extend_adjoin (ELL.isAlgebraic_j_over hK (ellEquiv (algebraMap K ℂ) hK 1))
    (M.val.comp (τ.toAlgHom.comp (inclusion (adjoin_j_le M hM _))))).choose

def galClassOfFun (τ : M ≃ₐ[K] M) : ClassGroup (𝓞 K) :=
  galClassHom hK (extendOf hK M hM τ)

theorem galClassOfFun_apply_j (τ : M ≃ₐ[K] M) (y : ELL K) :
    (τ ⟨ELL.j y, hM y⟩ : ℂ) =
      ELL.j ((ellMulAction (algebraMap K ℂ) hK).smul (galClassOfFun hK M hM τ) y) := by
  set x₀ := ellEquiv (algebraMap K ℂ) hK 1
  have hy : ELL.j y ∈ K⟮ELL.j x₀⟯ := ELL.j_mem_adjoin hK x₀ y
  have spec := (exists_algEquiv_extend_adjoin (ELL.isAlgebraic_j_over hK x₀)
    (M.val.comp (τ.toAlgHom.comp (inclusion (adjoin_j_le M hM x₀))))).choose_spec ⟨_, hy⟩
  rw [galClassOfFun, ← galClassHom_apply_j]
  exact spec.symm

theorem galClassOfFun_unique (τ : M ≃ₐ[K] M) (a : ClassGroup (𝓞 K)) (y : ELL K)
    (h : (τ ⟨ELL.j y, hM y⟩ : ℂ) = ELL.j ((ellMulAction (algebraMap K ℂ) hK).smul a y)) :
    galClassOfFun hK M hM τ = a := by
  rw [galClassOfFun_apply_j hK M hM] at h
  exact (existsUnique_smul_eq (algebraMap K ℂ) hK y _).unique (ELL.j_injective h) rfl

def galClassOf : (M ≃ₐ[K] M) →* ClassGroup (𝓞 K) where
  toFun := galClassOfFun hK M hM
  map_one' := by
    apply galClassOfFun_unique hK M hM 1 1 (ellEquiv (algebraMap K ℂ) hK 1)
    rw [ellMulAction_one_smul]
    rfl
  map_mul' τ₁ τ₂ := by
    set y := ellEquiv (algebraMap K ℂ) hK 1
    apply galClassOfFun_unique hK M hM _ _ y
    have h2 : τ₂ ⟨ELL.j y, hM y⟩ = ⟨ELL.j ((ellMulAction (algebraMap K ℂ) hK).smul
        (galClassOfFun hK M hM τ₂) y), hM _⟩ :=
      Subtype.ext (galClassOfFun_apply_j hK M hM τ₂ y)
    rw [ellMulAction_mul_smul, ← galClassOfFun_apply_j hK M hM τ₁, ← h2]
    rfl

theorem galClassOf_apply_j (τ : M ≃ₐ[K] M) (y : ELL K) :
    (τ ⟨ELL.j y, hM y⟩ : ℂ) =
      ELL.j ((ellMulAction (algebraMap K ℂ) hK).smul (galClassOf hK M hM τ) y) :=
  galClassOfFun_apply_j hK M hM τ y

end Field

theorem ELL.j_mem_algebraicClosure (y : ELL K) : ELL.j y ∈ algebraicClosure K ℂ :=
  mem_algebraicClosure_iff.2 (ELL.isAlgebraic_j_over hK y)

def galClassAlgClosure : (algebraicClosure K ℂ ≃ₐ[K] algebraicClosure K ℂ) →* ClassGroup (𝓞 K) :=
  galClassOf hK (algebraicClosure K ℂ) (ELL.j_mem_algebraicClosure hK)

section Adjoin

variable (x : ELL K)

def galClassAdjoin : (K⟮ELL.j x⟯ ≃ₐ[K] K⟮ELL.j x⟯) →* ClassGroup (𝓞 K) :=
  galClassOf hK K⟮ELL.j x⟯ (ELL.j_mem_adjoin hK x)

end Adjoin

end Elliptic
end GroundTheory.Global
