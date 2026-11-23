import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem semiBC_injective_of_injective : ∀ (A B : Type) [CommRing A] [CommRing B] (f : A →+* B),
    Function.Injective f → ∀ (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Projective A M] (N : Type) [AddCommGroup N] [Module B N] (u : M →ₛₗ[f] N),
    SemiBC u → Function.Injective u := by
  intro A B _ _ f hf M _ _ _ _ N _ _ u h
  obtain ⟨n, p, s, -, -, hps⟩ := Module.Finite.exists_comp_eq_id_of_projective A M
  let v : M →ₛₗ[f] (Fin n → B) :=
    { toFun := fun x i => f (s x i)
      map_add' := fun x y => by ext i; simp
      map_smul' := fun a x => by ext i; simp }
  obtain ⟨S, hS, -⟩ := h _ v
  rw [← LinearMap.ker_eq_bot (τ₁₂ := f), LinearMap.ker_eq_bot']
  intro x hx
  have h1 : v x = 0 := by rw [← hS, hx, map_zero]
  have h2 : s x = 0 := by
    funext i
    apply hf
    rw [Pi.zero_apply, map_zero]
    exact congrFun h1 i
  have h3 : x = p (s x) := by
    rw [← LinearMap.comp_apply, hps, LinearMap.id_apply]
  rw [h3, h2, map_zero]

end GlobalTheory.BSP
