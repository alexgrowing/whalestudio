import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory

theorem detLine_coord : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h N : ℕ) (ρ : Λ → Matrix (Fin h) (Fin h) O) (σ : Λ →+* O) (q : eig C ρ σ ≃ₗ[C] (Fin N → C)), (∀ x, x ∈ quotLattice C ρ σ ↔ ∀ i, q x i ∈ (algebraMap O C).range) → ∃ δ : detLine C ρ σ N ≃ₗ[C] C, (∀ x : Fin N → eig C ρ σ, δ (exteriorPower.ιMulti C N x) = (Matrix.of fun i => q (x i)).det) ∧ ∀ w, w ∈ detLattice C ρ σ N ↔ δ w ∈ (algebraMap O C).range := by
  intro C _ O _ _ Λ _ h N ρ σ q hq
  let b : Module.Basis (Fin N) C (eig C ρ σ) := Module.Basis.ofEquivFun q
  have hbq : ∀ v i, b.repr v i = q v i := fun v i => by
    simp only [b, Module.Basis.ofEquivFun_repr_apply]
  let f : detLine C ρ σ N →ₗ[C] C := exteriorPower.alternatingMapLinearEquiv b.det
  have hdet : ∀ x : Fin N → eig C ρ σ, f (exteriorPower.ιMulti C N x) = b.det x := fun x =>
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _
  have hfx : ∀ x : Fin N → eig C ρ σ,
      f (exteriorPower.ιMulti C N x) = (Matrix.of fun i => q (x i)).det := by
    intro x
    rw [hdet, Module.Basis.det_apply, ← Matrix.det_transpose]
    congr 1
  have hfb : f (exteriorPower.ιMulti C N b) = 1 := by rw [hdet, Module.Basis.det_self]
  have hall : ∀ w, f w • exteriorPower.ιMulti C N b = w := by
    intro w
    have hw : w ∈ Submodule.span C (exteriorPower.ιMulti C N ''
        {a : Fin N → eig C ρ σ | Set.range a ⊆ Set.range b}) := by
      rw [exteriorPower.ιMulti_span_of_span C N (eig C ρ σ) b.span_eq]; trivial
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      have hv : ∀ i, ∃ j, b j = a i := fun i => ha ⟨i, rfl⟩
      choose v hv using hv
      have hav : a = b ∘ v := funext fun i => (hv i).symm
      subst hav
      rw [hdet]
      by_cases hinj : Function.Injective v
      · let e : Equiv.Perm (Fin N) := Equiv.ofBijective v (Finite.injective_iff_bijective.mp hinj)
        have hve : (⇑b ∘ v) = ⇑b ∘ ⇑e := rfl
        rw [hve, AlternatingMap.map_perm, AlternatingMap.map_perm, Module.Basis.det_self]
        simp
      · rw [AlternatingMap.map_eq_zero_of_not_injective _ _ (fun h => hinj (Function.Injective.of_comp h)),
          AlternatingMap.map_eq_zero_of_not_injective _ _ (fun h => hinj (Function.Injective.of_comp h)),
          zero_smul]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, add_smul, hx, hy]
    | smul a x _ hx => rw [map_smul, smul_eq_mul, mul_smul, hx]
  let δ : detLine C ρ σ N ≃ₗ[C] C :=
    { f with
      invFun := fun c => c • exteriorPower.ιMulti C N b
      left_inv := hall
      right_inv := fun c => by
        show f (c • exteriorPower.ιMulti C N b) = c
        rw [map_smul, hfb, smul_eq_mul, mul_one] }
  refine ⟨δ, hfx, fun w => ⟨fun hw => ?_, fun hw => ?_⟩⟩
  · induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      have hy' : ∀ i j, ∃ o : O, algebraMap O C o = q (y i) j := fun i j => (hq (y i)).1 (hy i) j
      choose g hg using hy'
      show f _ ∈ _
      rw [hfx]
      refine ⟨(Matrix.of g).det, ?_⟩
      rw [RingHom.map_det]
      congr 1
      ext i j
      simp [RingHom.mapMatrix_apply, hg]
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      rw [map_add]; exact Subring.add_mem _ hx hy
    | smul a x _ hx =>
      rw [← algebraMap_smul C a x, map_smul, smul_eq_mul]
      exact Subring.mul_mem _ ⟨a, rfl⟩ hx
  · obtain ⟨o, ho⟩ := hw
    have hb : ∀ i, b i ∈ quotLattice C ρ σ := by
      intro i
      refine (hq (b i)).2 fun j => ?_
      rw [← hbq, Module.Basis.repr_self, Finsupp.single_apply]
      split_ifs
      · exact ⟨1, by simp⟩
      · exact ⟨0, by simp⟩
    have hw' : w = o • exteriorPower.ιMulti C N b := by
      rw [← algebraMap_smul C o, ho]
      exact (hall w).symm
    rw [hw']
    exact Submodule.smul_mem _ o (Submodule.subset_span ⟨b, hb, rfl⟩)

end GlobalTheory
