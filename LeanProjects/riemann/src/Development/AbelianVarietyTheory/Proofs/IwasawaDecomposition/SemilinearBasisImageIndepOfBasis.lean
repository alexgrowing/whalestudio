import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NuInRange
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Formalism.LocalRingCardinality.Lemmas

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory

theorem semilinear_basis_image_indep_of_basis :
    ∀ (K : Type) [Field K] (e : K →+* ℂ) (V : Type) [AddCommGroup V] [Module K V]
      (W : Type) [AddCommGroup W] [Module ℂ W] (j : V →ₛₗ[e] W) (ι κ : Type)
      (b : Module.Basis ι K V) (b' : Module.Basis κ K V),
      (LinearIndependent ℂ (fun i => j (b i)) ∧
        Submodule.span ℂ (Set.range fun i => j (b i)) = ⊤) →
      LinearIndependent ℂ (fun i => j (b' i)) ∧
        Submodule.span ℂ (Set.range fun i => j (b' i)) = ⊤ := by
  intro K _ e V _ _ W _ _ j ι κ b b' ⟨hli, hsp⟩
  letI : Algebra K ℂ := e.toAlgebra
  letI : Module K W := Module.compHom W e
  haveI : IsScalarTower K ℂ W := ⟨fun k c w => by
    change (e k * c) • w = e k • c • w
    exact mul_smul _ _ _⟩
  let j' : V →ₗ[K] W :=
    { toFun := j
      map_add' := j.map_add
      map_smul' := fun k v => j.map_smulₛₗ k v }
  let L : ℂ ⊗[K] V →ₗ[ℂ] W := j'.liftBaseChange ℂ
  have hL : ∀ v : V, L (1 ⊗ₜ[K] v) = j v := fun v => by
    simp [L, j']
  let c : Module.Basis ι ℂ W := Module.Basis.mk hli hsp.ge
  let E : ℂ ⊗[K] V ≃ₗ[ℂ] W := (b.baseChange ℂ).equiv c (Equiv.refl ι)
  have hE : (E : ℂ ⊗[K] V →ₗ[ℂ] W) = L := by
    refine (b.baseChange ℂ).ext fun i => ?_
    rw [LinearEquiv.coe_coe]
    simp only [E, Module.Basis.equiv_apply, Equiv.refl_apply, c, Module.Basis.mk_apply]
    rw [Module.Basis.baseChange_apply, hL]
  have hb : (fun i => j (b' i)) = ⇑((b'.baseChange ℂ).map E) := by
    funext i
    rw [Module.Basis.map_apply, Module.Basis.baseChange_apply, ← hL, ← hE, LinearEquiv.coe_coe]
  rw [hb]
  exact ⟨Module.Basis.linearIndependent _, Module.Basis.span_eq _⟩

end GlobalTheory
