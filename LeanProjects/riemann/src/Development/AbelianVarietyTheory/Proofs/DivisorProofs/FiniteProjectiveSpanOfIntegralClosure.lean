import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

open KaehlerDifferential in
private theorem projective_of_isScalarTower_projective (R A M : Type) [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] [Module.Projective R A]
    [Module.Projective A M] : Module.Projective R M := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective A M)
  have : Module.Projective R (M →₀ A) :=
    Module.Projective.of_equiv (finsuppLequivDFinsupp R : (M →₀ A) ≃ₗ[R] Π₀ _ : M, A).symm
  exact Module.Projective.of_split ((s.restrictScalars R))
    ((Finsupp.linearCombination A id).restrictScalars R)
    (LinearMap.ext fun m => LinearMap.congr_fun hs m)

open KaehlerDifferential in

theorem _root_.GlobalTheory.finite_projective_span_of_integralClosure :
    ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (A : Subalgebra k F) (B : Subalgebra k K), (∀ y : K, y ∈ B ↔ y ∈ integralClosure A K) → Module.Finite A (integralClosure A K) → Module.Projective A (integralClosure A K) → ∀ (W : Type) [AddCommGroup W] [Module K W] [Module F W] [IsScalarTower F K W] (S : Set W), (∀ c ∈ B, ∀ w ∈ S, (c : K) • w ∈ S) → Module.Finite B (Submodule.span B S) → Module.Projective B (Submodule.span B S) → Module.Finite A (Submodule.span A S) ∧ Module.Projective A (Submodule.span A S) := by
  intro k F K _ _ _ _ _ _ _ A B hB hfin hproj W _ _ _ _ S hS hfinB hprojB
  have hAB : ∀ a : A, algebraMap A K a ∈ B := fun a =>
    (hB _).2 ((integralClosure A K).algebraMap_mem a)
  letI : Algebra A B := ((algebraMap A K).codRestrict B hAB).toAlgebra
  have hcoe : ∀ (a : A) (b : B), ((a • b : B) : K) = algebraMap F K (a : F) * (b : K) := by
    intro a b
    rw [Algebra.smul_def]
    rfl
  haveI : IsScalarTower A B W := ⟨fun a b w => by
    rw [Subalgebra.smul_def, hcoe, mul_smul, algebraMap_smul, Subalgebra.smul_def,
      Subalgebra.smul_def]⟩
  let ψ : B ≃ₗ[A] integralClosure A K :=
    { toFun := fun b => ⟨b, (hB b).1 b.2⟩
      invFun := fun c => ⟨c, (hB c).2 c.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun a b => Subtype.ext <| by
        rw [hcoe, RingHom.id_apply, SetLike.val_smul, Algebra.smul_def]
        rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI : Module.Finite A B := Module.Finite.equiv ψ.symm
  haveI : Module.Projective A B := Module.Projective.of_equiv ψ.symm
  haveI : Module.Finite A (Submodule.span B S) := Module.Finite.trans B _
  haveI : Module.Projective A (Submodule.span B S) := projective_of_isScalarTower_projective A B _
  have hclosed : ∀ c : B, ∀ w ∈ Submodule.span A S, c • w ∈ Submodule.span A S := by
    intro c w hw
    induction hw using Submodule.span_induction with
    | mem s hs =>
      rw [Subalgebra.smul_def]
      exact Submodule.subset_span (hS c c.2 s hs)
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add v w _ _ hv hw => rw [smul_add]; exact Submodule.add_mem _ hv hw
    | smul a v _ hv => rw [smul_comm]; exact Submodule.smul_mem _ a hv
  let SB : Submodule B W :=
    { carrier := Submodule.span A S
      add_mem' := Submodule.add_mem _
      zero_mem' := Submodule.zero_mem _
      smul_mem' := fun c w hw => hclosed c w hw }
  have hsets : ∀ w, w ∈ Submodule.span A S ↔ w ∈ Submodule.span B S := by
    intro w
    constructor
    · intro hw
      have hle : Submodule.span A S ≤ (Submodule.span B S).restrictScalars A :=
        Submodule.span_le.mpr fun s hs => Submodule.subset_span hs
      exact hle hw
    · intro hw
      have hle : Submodule.span B S ≤ SB :=
        Submodule.span_le.mpr fun s hs => (Submodule.subset_span hs : s ∈ Submodule.span A S)
      exact hle hw
  let χ : Submodule.span A S ≃ₗ[A] Submodule.span B S :=
    { toFun := fun w => ⟨w, (hsets w).1 w.2⟩
      invFun := fun w => ⟨w, (hsets w).2 w.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact ⟨Module.Finite.equiv χ.symm, Module.Projective.of_equiv χ.symm⟩

end GlobalTheory
