import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.GenModelXi
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2

noncomputable section
open scoped BigOperators

namespace Formalism.L2.PairingIndexBounds.Mv

open Formalism.L2.Th1.H

section
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem altE_add_left (H : Sesq V) (a a' b : V) : altE H (a + a') b = altE H a b + altE H a' b := by
  simp [altE, map_add, LinearMap.add_apply, Complex.add_im]

theorem altE_add_right (H : Sesq V) (a b b' : V) : altE H a (b + b') = altE H a b + altE H a b' := by
  simp [altE, map_add, Complex.add_im]

theorem opU_smul_fun (H : Sesq V) (x : V) (r : ℂ) (F : V → ℂ) (z : V) :
    opU H x (fun v => r * F v) z = r * opU H x F z := by
  simp only [opU]; ring

end

theorem heisenberg_unitary_holds : HeisU := by
  intro V _ _ H α A B hH hA hB
  have hA0 := (semiCharBasic V H hH A α hA).1
  refine ⟨⟨fun b a => Complex.exp_ne_zero _, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro b b' a
    simp only [cU, AddSubgroup.coe_add, altE_add_right, Complex.ofReal_add, ← Complex.exp_add]
    congr 1; ring
  · intro b a a'
    simp only [cU, AddSubgroup.coe_add, altE_add_left, Complex.ofReal_add, ← Complex.exp_add]
    congr 1; ring
  · ext F z
    simp only [wA, wU, LinearMap.coe_mk, AddHom.coe_mk, ZeroMemClass.coe_zero, LinearMap.id_coe, id_eq, hA0, one_mul]
    exact ((opUComm V H hH F z).1)
  · intro a a'
    ext F z
    simp only [wA, wU, LinearMap.coe_mk, AddHom.coe_mk, AddSubgroup.coe_add, LinearMap.coe_comp, Function.comp_apply]
    exact (semiHom V H hH A α hA a a.2 a' a'.2 F z).symm
  · have hB0 := (semiCharBasic V H hH B α hB).1
    ext F z
    simp only [wB, wU, LinearMap.coe_mk, AddHom.coe_mk, ZeroMemClass.coe_zero, LinearMap.id_coe, id_eq, hB0, one_mul]
    exact ((opUComm V H hH F z).1)
  · intro b b'
    ext F z
    simp only [wB, wU, LinearMap.coe_mk, AddHom.coe_mk, AddSubgroup.coe_add, LinearMap.coe_comp, Function.comp_apply]
    exact (semiHom V H hH B α hB b b.2 b' b'.2 F z).symm
  · intro a b
    ext F z
    simp only [wA, wB, wU, cU, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    rw [opU_smul_fun, opU_smul_fun, (opUComm V H hH F z).2 (a : V) (b : V)]
    ring

theorem self_intersection_holds : InterSelf := by
  intro V _ _ H α Λ hH hΛ θ hθ
  funext z
  have hS : IsReps Λ Λ {0} := by
    refine ⟨fun x hx => ?_, fun x hx y hy _ => ?_, fun y hy => ⟨0, by simp, by simpa using hy⟩⟩
    · rw [Finset.mem_singleton] at hx; rw [hx]; exact Λ.zero_mem
    · rw [Finset.mem_singleton] at hx hy; rw [hx, hy]
  rw [interReps V H hH Λ Λ α hΛ θ hθ {0} hS z]
  have h1 : relIdx Λ Λ = 1 := by simp [relIdx]
  have hA0 := (semiCharBasic V H hH Λ α hΛ).1
  simp only [h1, Nat.cast_one, Real.sqrt_one, Complex.ofReal_one, inv_one, one_mul, sumU, Finset.sum_singleton, hA0]
  exact (opUComm V H hH θ z).1

end Formalism.L2.PairingIndexBounds.Mv
