import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem rpML {X M : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M] (n : ℕ)
    (b : Fin n → X →ₗ[ℂ] Module.End ℂ M) :
    ∃ R : MultilinearMap ℂ (fun _ : Fin n => X) (Module.End ℂ M), ∀ x, R x = rp n b x := by
  induction n with
  | zero => exact ⟨MultilinearMap.constOfIsEmpty ℂ _ 1, fun _ => rfl⟩
  | succ n ih =>
    obtain ⟨R, hR⟩ := ih (Fin.tail b)
    let g : X →ₗ[ℂ] MultilinearMap ℂ (fun _ : Fin n => X) (Module.End ℂ M) :=
      { toFun := fun x0 => (LinearMap.mulRight ℂ (b 0 x0)).compMultilinearMap R
        map_add' := fun u v => MultilinearMap.ext fun y => by simp [mul_add]
        map_smul' := fun c u => MultilinearMap.ext fun y => by simp }
    refine ⟨LinearMap.uncurryLeft (R := ℂ) (M := fun _ : Fin (n + 1) => X) g, fun x => ?_⟩
    rw [rp_succ, ← hR]
    rfl

theorem UpperTheory.V.AlgRepEndIrreducible.telML :
    ∀ (X M : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M] (n : ℕ) (a b : Fin n → X →ₗ[ℂ] Module.End ℂ M),
      ∃ T : (X →ₗ[ℂ] M) →ₗ[ℂ] MultilinearMap ℂ (fun _ : Fin n => X) M, ∀ f x, T f x = tel n a b f x := by
  intro X M _ _ _ _ n a b
  induction n with
  | zero => exact ⟨0, fun _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨T, hT⟩ := ih (Fin.tail a) (Fin.tail b)
    obtain ⟨R, hR⟩ := rpML n (Fin.tail b)
    let g : (X →ₗ[ℂ] M) → X →ₗ[ℂ] MultilinearMap ℂ (fun _ : Fin n => X) M := fun f =>
      { toFun := fun x0 => (a 0 x0).compMultilinearMap (T f) +
          (LinearMap.applyₗ (f x0) : Module.End ℂ M →ₗ[ℂ] M).compMultilinearMap R
        map_add' := fun u v => MultilinearMap.ext fun y => by simp; abel
        map_smul' := fun c u => MultilinearMap.ext fun y => by simp }
    have hg : ∀ (f : X →ₗ[ℂ] M) (x : Fin (n + 1) → X), LinearMap.uncurryLeft (R := ℂ) (M := fun _ : Fin (n + 1) => X) (g f) x =
        a 0 (x 0) (T f (Fin.tail x)) + R (Fin.tail x) (f (x 0)) := by
      intro f x
      rfl
    refine ⟨{ toFun := fun f => LinearMap.uncurryLeft (R := ℂ) (M := fun _ : Fin (n + 1) => X) (g f)
              map_add' := fun u v => MultilinearMap.ext fun y => ?_
              map_smul' := fun c u => MultilinearMap.ext fun y => ?_ }, fun f x => ?_⟩
    · simp only [MultilinearMap.add_apply, hg, map_add, LinearMap.add_apply]
      abel
    · simp only [MultilinearMap.smul_apply, hg, map_smul, LinearMap.smul_apply, RingHom.id_apply, smul_add]
    · rw [tel_succ, ← hT, ← hR]
      exact hg f x
