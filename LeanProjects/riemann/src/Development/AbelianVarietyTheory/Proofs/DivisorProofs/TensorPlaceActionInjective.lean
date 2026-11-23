import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpanTprodOfCommuteAtEachPlace
open scoped TensorProduct

namespace GlobalTheory.FactorKernel

variable {ι : Type} [Fintype ι] [hd : DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V]

noncomputable def contrML (w₀ : ι) (μ : ι → Module.Dual ℂ V) : MultilinearMap ℂ (fun _ : ι => V) V where
  toFun x := (∏ i ∈ Finset.univ.erase w₀, μ i (x i)) • x w₀
  map_update_add' := by
    intro inst x i a b
    obtain rfl : inst = hd := Subsingleton.elim _ _
    by_cases h : i = w₀
    · subst h
      have e : ∀ c, ∏ k ∈ Finset.univ.erase i, μ k (Function.update x i c k) =
          ∏ k ∈ Finset.univ.erase i, μ k (x k) := fun c =>
        Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
      simp only [e, Function.update_self, smul_add]
    · have hi : i ∈ Finset.univ.erase w₀ := Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩
      have e : ∀ c, ∏ k ∈ Finset.univ.erase w₀, μ k (Function.update x i c k) =
          μ i c * ∏ k ∈ (Finset.univ.erase w₀).erase i, μ k (x k) := fun c => by
        rw [← Finset.mul_prod_erase _ _ hi, Function.update_self]
        congr 1
        exact Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
      simp only [e, Function.update_of_ne (Ne.symm h), map_add, add_mul, add_smul]
  map_update_smul' := by
    intro inst x i c a
    obtain rfl : inst = hd := Subsingleton.elim _ _
    by_cases h : i = w₀
    · subst h
      have e : ∀ c, ∏ k ∈ Finset.univ.erase i, μ k (Function.update x i c k) =
          ∏ k ∈ Finset.univ.erase i, μ k (x k) := fun c =>
        Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
      simp only [e, Function.update_self, smul_comm c]
    · have hi : i ∈ Finset.univ.erase w₀ := Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩
      have e : ∀ c, ∏ k ∈ Finset.univ.erase w₀, μ k (Function.update x i c k) =
          μ i c * ∏ k ∈ (Finset.univ.erase w₀).erase i, μ k (x k) := fun c => by
        rw [← Finset.mul_prod_erase _ _ hi, Function.update_self]
        congr 1
        exact Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
      simp only [e, Function.update_of_ne (Ne.symm h), map_smul, smul_eq_mul, mul_assoc, smul_smul]

noncomputable def contr (w₀ : ι) (μ : ι → Module.Dual ℂ V) : (⨂[ℂ] _ : ι, V) →ₗ[ℂ] V :=
  PiTensorProduct.lift (contrML w₀ μ)

theorem contr_tprod (w₀ : ι) (μ : ι → Module.Dual ℂ V) (x : ι → V) :
    contr w₀ μ (PiTensorProduct.tprod ℂ x) = (∏ i ∈ Finset.univ.erase w₀, μ i (x i)) • x w₀ := by
  rw [contr, PiTensorProduct.lift.tprod]; rfl

theorem dual_contr (w₀ : ι) (μ : ι → Module.Dual ℂ V) (ν : Module.Dual ℂ V) (T : ⨂[ℂ] _ : ι, V) :
    ν (contr w₀ μ T) =
      PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ (Function.update μ w₀ ν)) T := by
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [map_smul, map_smul, map_smul, contr_tprod, PiTensorProduct.dualDistrib_apply, map_smul,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ w₀), Function.update_self, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    congr 1
    rw [mul_comm]
    congr 1
    exact Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]

theorem contr_atPl (w₀ : ι) (μ : ι → Module.Dual ℂ V) (L : Module.End ℂ V) (T : ⨂[ℂ] _ : ι, V) :
    contr w₀ μ (GlobalTheory.RealLift.atPl (V := fun _ : ι => V) w₀ L T) = L (contr w₀ μ T) := by
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [map_smul, map_smul, map_smul, GlobalTheory.RealLift.atPl, PiTensorProduct.map_tprod, contr_tprod, contr_tprod,
      map_smul, Function.update_self, L.map_smul]
    congr 2
    exact Finset.prod_congr rfl fun k hk => by
      simp [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem atPl_noCommonKernel : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (V : Type) [AddCommGroup V] [Module ℂ V] (J : Type)
    (L : J → Module.End ℂ V) (w₀ : ι), (∀ v : V, (∀ j, L j v = 0) → v = 0) →
    ∀ T : ⨂[ℂ] _ : ι, V, (∀ j, GlobalTheory.RealLift.atPl (V := fun _ : ι => V) w₀ (L j) T = 0) → T = 0 := by
  intro ι _ _ V _ _ J L w₀ hL T hT
  apply GlobalTheory.PiTensorCommute.eq_zero_of_forall_dualDistrib (M := fun _ : ι => V)
  intro f
  have hv : contr w₀ f T = 0 := hL _ fun j => by rw [← contr_atPl, hT j, map_zero]
  have h := dual_contr w₀ f (f w₀) T
  rw [hv, map_zero, Function.update_eq_self] at h
  exact h.symm

end GlobalTheory.FactorKernel
