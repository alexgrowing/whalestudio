import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR.TensQuad

variable {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)]

theorem atPl_tprod (w : T) (L : Module.End ℂ (V w)) (f : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f w (L (f w))) := by
  rw [atPl, PiTensorProduct.map_tprod]
  congr 1
  funext i
  rcases eq_or_ne i w with rfl | h
  · simp
  · simp [Function.update_of_ne h]

noncomputable def atPlLin (w : T) : Module.End ℂ (V w) →ₗ[ℂ] Module.End ℂ (⨂[ℂ] i, V i) :=
  (PiTensorProduct.mapMultilinear ℂ V V).toLinearMap (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w

theorem atPlLin_apply (w : T) (L : Module.End ℂ (V w)) : atPlLin w L = atPl w L := rfl

theorem atPl_mul (w : T) (L₁ L₂ : Module.End ℂ (V w)) : atPl w (L₁ * L₂) = atPl w L₁ * atPl w L₂ := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro f
  simp [atPl_tprod, Module.End.mul_apply]

theorem atPl_one (w : T) : atPl w (1 : Module.End ℂ (V w)) = 1 := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro f
  simp [atPl_tprod]

theorem qop_atPl {ι : Type} [Fintype ι] [DecidableEq ι] (w : T) (F : ι → ι → Module.End ℂ (V w)) (α β : ℂ) (i j : ι) :
    qop (fun a b => atPl w (F a b)) α β i j = atPl w (qop F α β i j) := by
  simp only [qop, ← atPlLin_apply, map_sub, map_sum, map_smul, apply_ite (atPlLin w), map_zero]
  simp only [atPlLin_apply, atPl_mul, atPl_one]

theorem mem_of_atPl (C : ∀ w, Submodule ℂ (V w)) (w : T) (L : Module.End ℂ (V w)) (hL : ∀ x, L x ∈ C w)
    (v : ⨂[ℂ] i, V i) : atPl w L v ∈ tensAny C := by
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, atPl_tprod]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨w, by simpa using hL (f w)⟩, rfl⟩)
  | add x y hx hy =>
    rw [map_add]
    exact add_mem hx hy

end GlobalTheory.HoweR.TensQuad

open GlobalTheory.HoweR.TensQuad in
theorem GlobalTheory.HoweR.quadMod_actAt : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)], ∀ (C : ∀ w, Submodule ℂ (V w)) (w : T) (p q : ℕ) (a : Mat p q →ₗ[ℂ] Module.End ℂ (V w)) (α β α' β' : ℂ), QuadMod a α β α' β' (C w) ⊤ → QuadMod (actAt w a) α β α' β' (tensAny C) ⊤ := by
  intro T _ _ V _ _ C w p q a α β α' β' h i j v _
  have hu : units (actAt w a) = fun i j => atPl w (units a i j) := rfl
  have hn : negT (units (actAt w a)) = fun i j => atPl w (negT (units a) i j) := by
    funext i j
    simp only [negT, units, actAt_apply, ← atPlLin_apply, map_neg]
  refine ⟨?_, ?_⟩
  · rw [hu, qop_atPl]
    exact mem_of_atPl C w _ (fun x => (h i j x Submodule.mem_top).1) v
  · rw [hn, qop_atPl]
    exact mem_of_atPl C w _ (fun x => (h i j x Submodule.mem_top).2) v
