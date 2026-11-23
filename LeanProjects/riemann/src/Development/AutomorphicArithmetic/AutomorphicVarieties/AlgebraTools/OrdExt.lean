import Mathlib

open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.ord_ext :
    ∀ {R Γ E : Type} [CommRing R] [Monoid Γ] [Ring E] [Algebra R E] {n : ℕ} (r : Γ →* E) (ψ : Fin n → Γ →* R), (∀ g : Fin n → Γ, (List.ofFn fun i => r (g i) - algebraMap R E (ψ i (g i))).prod = 0) → ∀ z : Fin n → MonoidAlgebra R Γ, (List.ofFn fun i => MonoidAlgebra.lift R E Γ r (z i) - algebraMap R E (MonoidAlgebra.lift R R Γ (ψ i) (z i))).prod = 0 := by
  intro R Γ E _ _ _ _ n r ψ h z
  let φ : Fin n → (MonoidAlgebra R Γ →ₗ[R] E) := fun i =>
    (MonoidAlgebra.lift R E Γ r).toLinearMap -
      (Algebra.linearMap R E).comp (MonoidAlgebra.lift R R Γ (ψ i)).toLinearMap
  let F : MultilinearMap R (fun _ : Fin n => MonoidAlgebra R Γ) E :=
    (MultilinearMap.mkPiAlgebraFin R n E).compLinearMap φ
  have hF : F = 0 := by
    refine Module.Basis.ext_multilinear (f := F) (g := 0)
      (fun _ => MonoidAlgebra.basis Γ R) ?_
    intro v
    simp only [F, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebraFin_apply,
      MultilinearMap.zero_apply, MonoidAlgebra.basis_apply]
    convert h v using 3
    funext i
    simp [φ, MonoidAlgebra.lift_single]
  have := congrArg (fun G => G z) hF
  simpa [F, φ] using this
