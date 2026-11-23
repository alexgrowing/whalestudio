import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IsCplAtSelf
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplMap

open IsLocalRing UpperTheory.V.AlgebraTools TensorProduct

private theorem rTensor_inj_of_map {Λ : Type} [CommRing Λ] (p : Ideal Λ) {L : Type} [CommRing L]
    [Algebra Λ L] (m : Ideal L) (hm : p.map (algebraMap Λ L) = m)
    (N : Type) [AddCommGroup N] [Module Λ N] [Module L N] [IsScalarTower Λ L N]
    [Module.Flat Λ N] : Function.Injective (m.subtype.rTensor N) := by
  have hmem : ∀ a : p, algebraMap Λ L a ∈ m := fun a => hm ▸ Ideal.mem_map_of_mem _ a.2
  let ι : p →+ m :=
    { toFun := fun a => ⟨algebraMap Λ L a, hmem a⟩
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp }
  let σ : p ⊗[Λ] N →+ m ⊗[L] N :=
    TensorProduct.liftAddHom
      (AddMonoidHom.mk' (fun a => (TensorProduct.mk L m N (ι a)).toAddMonoidHom)
        (fun a b => by ext n; simp [TensorProduct.add_tmul]))
      (fun r a n => by
        change ι (r • a) ⊗ₜ[L] n = ι a ⊗ₜ[L] (r • n)
        have h : ι (r • a) = algebraMap Λ L r • ι a := by
          apply Subtype.ext
          change algebraMap Λ L (r • (a : Λ)) = algebraMap Λ L r * algebraMap Λ L a
          rw [smul_eq_mul, map_mul]
        rw [h, TensorProduct.smul_tmul, algebraMap_smul])
  have key : ∀ y, y ∈ Submodule.span L (algebraMap Λ L '' (p : Set Λ)) →
      ∀ (hy : y ∈ m) (n : N), (⟨y, hy⟩ : m) ⊗ₜ[L] n ∈ σ.range := by
    intro y hy'
    induction hy' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      intro hy n
      exact AddMonoidHom.mem_range.mpr ⟨(⟨a, ha⟩ : p) ⊗ₜ[Λ] n, by
        rw [TensorProduct.liftAddHom_tmul]; rfl⟩
    | zero =>
      intro hy n
      have h : (⟨0, hy⟩ : m) = 0 := rfl
      rw [h, TensorProduct.zero_tmul]
      exact zero_mem _
    | add y₁ y₂ h₁ h₂ ih₁ ih₂ =>
      intro hy n
      have m₁ : y₁ ∈ m := by rw [← hm]; exact h₁
      have m₂ : y₂ ∈ m := by rw [← hm]; exact h₂
      have h : (⟨y₁ + y₂, hy⟩ : m) = ⟨y₁, m₁⟩ + ⟨y₂, m₂⟩ := rfl
      rw [h, TensorProduct.add_tmul]
      exact add_mem (ih₁ m₁ n) (ih₂ m₂ n)
    | smul l y h₁ ih =>
      intro hy n
      have m₁ : y ∈ m := by rw [← hm]; exact h₁
      have h : (⟨l • y, hy⟩ : m) = l • ⟨y, m₁⟩ := rfl
      rw [h, TensorProduct.smul_tmul]
      exact ih m₁ (l • n)
  have hsurj : ∀ z : m ⊗[L] N, z ∈ σ.range := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | tmul a n =>
      exact key a.1 (show (a : L) ∈ p.map (algebraMap Λ L) by rw [hm]; exact a.2) a.2 n
    | add x y hx hy => exact add_mem hx hy
  have hcomp : ∀ w : p ⊗[Λ] N, TensorProduct.lid L N (m.subtype.rTensor N (σ w))
      = TensorProduct.lid Λ N (p.subtype.rTensor N w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a n =>
      rw [TensorProduct.liftAddHom_tmul]
      change TensorProduct.lid L N (m.subtype.rTensor N ((⟨algebraMap Λ L a, hmem a⟩ : m) ⊗ₜ[L] n))
        = _
      simp [algebraMap_smul]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨w, rfl⟩ := AddMonoidHom.mem_range.mp (hsurj z)
  have hw : p.subtype.rTensor N w = 0 := by
    apply (TensorProduct.lid Λ N).injective
    rw [← hcomp, hz, map_zero, map_zero]
  have hw0 : w = 0 := Module.Flat.rTensor_preserves_injective_linearMap p.subtype
    Subtype.val_injective (by rw [hw, map_zero])
  rw [hw0, map_zero]

theorem UpperTheory.V.AlgebraTools.IsCplAt.free_of_flat :
    ∀ (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] (p : Ideal Λ) (L : Type) [CommRing L] [IsLocalRing L] [Algebra Λ L]
      (N : Type) [AddCommGroup N] [Module Λ N] [Module L N] [IsScalarTower Λ L N] [Module.Finite L N]
      [Module.Flat Λ N], IsCplAt Λ p L → Module.Free L N := by
  intro Λ _ _ p L _ _ _ N _ _ _ _ _ _ h
  haveI := h.noeth
  haveI : Module.FinitePresentation L N := Module.finitePresentation_of_finite L N
  apply Module.free_of_maximalIdeal_rTensor_injective
  exact rTensor_inj_of_map p _ (by simpa using IsCplAt.map_pow_eq Λ p L h 1) N
