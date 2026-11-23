import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.HomTrace

theorem finiteDimensional_of_hom (W H : Type) [AddCommGroup W] [Module ℂ W]
    [AddCommGroup H] [Module ℂ H] [Nontrivial W] [FiniteDimensional ℂ (W →ₗ[ℂ] H)] :
    FiniteDimensional ℂ H := by
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  have hex : ∃ φ : Module.Dual ℂ W, φ w ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hw ((Module.forall_dual_apply_eq_zero_iff ℂ w).1 hcon)
  obtain ⟨φ, hφ⟩ := hex
  let j : H →ₗ[ℂ] (W →ₗ[ℂ] H) :=
    { toFun := fun h => φ.smulRight h
      map_add' := fun x y => by ext v; simp
      map_smul' := fun c x => by
        ext v
        simp only [LinearMap.smulRight_apply, LinearMap.smul_apply, RingHom.id_apply]
        exact smul_comm _ _ _ }
  have hj : Function.Injective j := by
    intro x y hxy
    have h1 : φ w • x = φ w • y := by
      simpa [j] using LinearMap.congr_fun hxy w
    exact smul_right_injective H hφ h1
  exact FiniteDimensional.of_injective j hj

noncomputable def sandwich {W H : Type} [AddCommGroup W] [Module ℂ W]
    [AddCommGroup H] [Module ℂ H] (a : H →ₗ[ℂ] H) (b : W →ₗ[ℂ] W) :
    (W →ₗ[ℂ] H) →ₗ[ℂ] (W →ₗ[ℂ] H) where
  toFun f := a ∘ₗ f ∘ₗ b
  map_add' f g := by ext v; simp
  map_smul' c f := by ext v; simp

@[simp] theorem sandwich_apply {W H : Type} [AddCommGroup W] [Module ℂ W]
    [AddCommGroup H] [Module ℂ H] (a : H →ₗ[ℂ] H) (b : W →ₗ[ℂ] W) (f : W →ₗ[ℂ] H) :
    sandwich a b f = a ∘ₗ f ∘ₗ b := rfl

theorem trace_sandwich {W H : Type} [AddCommGroup W] [Module ℂ W]
    [AddCommGroup H] [Module ℂ H] [FiniteDimensional ℂ W] [FiniteDimensional ℂ H]
    (a : H →ₗ[ℂ] H) (b : W →ₗ[ℂ] W) :
    LinearMap.trace ℂ (W →ₗ[ℂ] H) (sandwich a b) =
      LinearMap.trace ℂ W b * LinearMap.trace ℂ H a := by
  let e := dualTensorHomEquiv ℂ W H
  let M : (TensorProduct ℂ (Module.Dual ℂ W) H) →ₗ[ℂ] (TensorProduct ℂ (Module.Dual ℂ W) H) :=
    TensorProduct.map (Module.Dual.transpose (R := ℂ) b) a
  have hcomp : (e : _ →ₗ[ℂ] _) ∘ₗ M = sandwich a b ∘ₗ (e : _ →ₗ[ℂ] _) := by
    apply TensorProduct.ext'
    intro φ h
    ext v
    simp [e, M, dualTensorHomEquiv, dualTensorHomEquivOfBasis_apply, dualTensorHom_apply,
      Module.Dual.transpose_apply]
  have hconj : e.conj M = sandwich a b := by
    rw [LinearEquiv.conj_apply]
    ext1 f
    have := LinearMap.congr_fun hcomp (e.symm f)
    simpa using this
  rw [← hconj, LinearMap.trace_conj', LinearMap.trace_tensorProduct', LinearMap.trace_transpose']

end GlobalTheory.CompanionTheory.HomTrace
