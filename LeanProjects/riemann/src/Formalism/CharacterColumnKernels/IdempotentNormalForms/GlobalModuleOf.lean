import Formalism.CharacterColumnKernels.StatGlobalModule
import Formalism.CharacterColumnKernels.IdempotentNormalForms.GlobalConcreteOf
import Formalism.CharacterColumnKernels.IdempotentNormalForms.GenFin
import Formalism.CharacterColumnKernels.IdempotentNormalForms.CupKillAdm

open Finset

noncomputable section

namespace Formalism.NG

universe u v w x

theorem globalModule_of (hF : StatFinPres.{max u w, x}) : StatGlobalModule.{u, v, w, x} := by
  intro O _ _ _ X X' T T' Z p q b hT hZ d _ _ R' _ hdet NN _ _ g₀ n hspan hφ π' ρπ hρπ α _ _ bl hbl
    ρk hsurj hblk _ hcard
  obtain ⟨m, P, ⟨eM⟩⟩ := hF R' NN g₀ n hspan
  have hφ' : ∀ x', p x' ∉ Z → ∃ φ : Coker P →ₗ[R'] EvalSp O d R' x', φ ≠ 0 := by
    intro x' hx
    obtain ⟨φ, hφ0⟩ := hφ x' hx
    refine ⟨φ.comp eM.symm.toLinearMap, fun h => hφ0 ?_⟩
    refine LinearMap.ext fun y => ?_
    have hy := LinearMap.congr_fun h (eM y)
    simpa using hy
  have hcard' : ((Fintype.card (Fin g₀) * ∑ k : α, Fintype.card {a // bl a = k} : ℕ) : Cardinal) <
      Cardinal.mk (IsLocalRing.ResidueField O) := by
    rw [Fintype.card_fin]
    exact hcard
  refine (globalConcrete O X X' T T' Z p q b hT hZ d R' (Fin m) (Fin g₀) P (fun Θ => hdet (Fin g₀) Θ)
    hφ' π' ρπ hρπ α bl hbl ρk hsurj hblk hcard').trans
    (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
  have hk := kerHomRect R' O (Fin m) (Fin g₀) {a // bl a = k} (ρk k).toRingHom P
  let eqv : (Coker P →ₗ[R'] LatQ O {a // bl a = k} (ρk k).toRingHom) ≃ₗ[O]
      (NN →ₗ[R'] LatQ O {a // bl a = k} (ρk k).toRingHom) :=
    { toFun := fun f => f.comp eM.toLinearMap
      invFun := fun f => f.comp eM.symm.toLinearMap
      map_add' := fun _ _ => LinearMap.ext fun _ => rfl
      map_smul' := fun _ _ => LinearMap.ext fun _ => rfl
      left_inv := fun f => LinearMap.ext fun y => congrArg f (eM.apply_symm_apply y)
      right_inv := fun f => LinearMap.ext fun y => congrArg f (eM.symm_apply_apply y) }
  exact hk.trans eqv.length_eq

theorem globalModule : StatGlobalModule := globalModule_of finPres

end Formalism.NG
