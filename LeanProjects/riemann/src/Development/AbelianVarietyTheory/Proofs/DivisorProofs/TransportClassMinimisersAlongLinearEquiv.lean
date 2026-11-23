import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
open GlobalTheory.PolFan GlobalTheory.LocM

namespace GlobalTheory

theorem transport_cong {N r : ℕ} (e : (Fin r → ℤ) →ₗ[ℤ] (Fin r → ℤ)) (x y : Fin r → ℤ)
    (h : ∀ i, ((x i : ℤ) : ZMod N) = y i) : ∀ i, ((e x i : ℤ) : ZMod N) = e y i := by
  have hd : ∀ i, (N : ℤ) ∣ x i - y i := fun i => (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (h i).symm
  choose w hw using hd
  have hxy : x - y = (N : ℤ) • w := by ext i; simp [hw i]
  have he : e x - e y = (N : ℤ) • e w := by rw [← map_sub, hxy, map_smul]
  intro i
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  have := congrFun he i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
  exact ⟨-(e w i), by linarith⟩

theorem transport_minimisers : ∀ (O : Type) [CommRing O] (X Y : Type) [AddCommGroup X] [Module O X] [AddCommGroup Y] [Module O Y] (n N : ℕ) [NeZero N] (ebX : X ≃ₗ[ℤ] (Fin n → ℤ)) (ebY : Y ≃ₗ[ℤ] (Fin n → ℤ)) (f : X ≃ₗ[O] Y) (μ : (Fin n → ZMod N) → Y), (∀ cl i, ((ebY (μ cl) i : ℤ) : ZMod N) = cl i) → ∃ σ : Equiv.Perm (Fin n → ZMod N), (∀ cl i, ((ebX (f.symm (μ (σ cl))) i : ℤ) : ZMod N) = cl i) ∧ ∀ b : LinearMap.BilinForm ℤ Y, (∀ cl (α : Y), (∀ i, ((ebY α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α) → ∀ cl (α : X), (∀ i, ((ebX α i : ℤ) : ZMod N) = cl i) → pull f.toLinearMap b (f.symm (μ (σ cl))) (f.symm (μ (σ cl))) ≤ pull f.toLinearMap b α α := by
  intro O _ X Y _ _ _ _ n N _ ebX ebY f μ hμ
  let A : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ) :=
    ebY.toLinearMap ∘ₗ f.toLinearMap.toAddMonoidHom.toIntLinearMap ∘ₗ ebX.symm.toLinearMap
  let B : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ) :=
    ebX.toLinearMap ∘ₗ f.symm.toLinearMap.toAddMonoidHom.toIntLinearMap ∘ₗ ebY.symm.toLinearMap
  have hA : ∀ x, A x = ebY (f (ebX.symm x)) := fun x => rfl
  have hB : ∀ x, B x = ebX (f.symm (ebY.symm x)) := fun x => rfl
  have hBA : ∀ x, B (A x) = x := fun x => by simp [hA, hB]
  have hAB : ∀ x, A (B x) = x := fun x => by simp [hA, hB]
  have key : ∀ (F G : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ)), (∀ x, G (F x) = x) → ∀ c i,
      ((G (ebY (μ (fun i => ((F (ebY (μ c)) i : ℤ) : ZMod N)))) i : ℤ) : ZMod N) = c i := by
    intro F G hGF c i
    rw [transport_cong G _ (F (ebY (μ c))) (fun j => hμ _ j) i, hGF, hμ]
  let σ : Equiv.Perm (Fin n → ZMod N) :=
    { toFun := fun c i => ((A (ebY (μ c)) i : ℤ) : ZMod N)
      invFun := fun c i => ((B (ebY (μ c)) i : ℤ) : ZMod N)
      left_inv := fun c => by funext i; exact key A B hBA c i
      right_inv := fun c => by funext i; exact key B A hAB c i }
  refine ⟨σ, fun c i => ?_, ?_⟩
  · have := key A B hBA c i
    rw [hB, LinearEquiv.symm_apply_apply] at this
    exact this
  · intro b hmin c α hα
    simp only [pull_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    apply hmin (σ c) (f α)
    intro i
    have h1 : ebY (f α) = A (ebX α) := by rw [hA, LinearEquiv.symm_apply_apply]
    rw [h1]
    exact transport_cong A (ebX α) (ebY (μ c)) (fun j => (hα j).trans (hμ c j).symm) i

end GlobalTheory
