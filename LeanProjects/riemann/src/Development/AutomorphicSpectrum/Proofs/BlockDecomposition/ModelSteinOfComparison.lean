import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftSemiTmul

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB

theorem comparison_degree_one_tensor_coboundary {R k C : Type} [CommRing R] [CommRing k] [Algebra R k] [Category.{0} C]
    {F : C ⥤ CommAlgCat.{0} R} {F' : C ⥤ CommAlgCat.{0} k} (m : BC F F') (y : k ⊗[R] C0 F) :
    th1 m ((d0 F).lTensor k y) = d0 F' (th0 m y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul s f =>
    rw [LinearMap.lTensor_tmul, th1, th0, liftSemi_tmul, liftSemi_tmul, map_smul]
    congr 1
    funext T T' φ
    change m.α T' (d0 F f T T' φ) = d0 F' (c0 m f) T T' φ
    rw [amitsur_d0_apply, amitsur_d0_apply, map_sub, m.naturality]
    rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem const_on_fibre : ∀ (R k C P₀ P₁ P₂ : Type) [CommRing R] [Field k] [Algebra R k] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} k) [AddCommGroup P₀] [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂] (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (ψ₀ : P₀ →ₗ[R] C0 F) (ψ₁ : P₁ →ₗ[R] C1 F) (ψ₂ : P₂ →ₗ[R] C2 F) (m : BC F F') (e : P₀), IsModel F a₀ a₁ ψ₀ ψ₁ ψ₂ → Function.Bijective (th0 m) → Stein F' → a₀ e = 0 → ψ₀ e = 1 → ∀ x : k ⊗[R] P₀, a₀.lTensor k x = 0 → ∃ c : k, x = c • ((1 : k) ⊗ₜ[R] e) := by
  intro R k C P₀ P₁ P₂ _ _ _ _ F F' _ _ _ _ _ _ a₀ a₁ ψ₀ ψ₁ ψ₂ m e hM hb hS ha he x hx
  obtain ⟨-, h2, -, hQ⟩ := hM
  have hx1 : (d0 F).lTensor k (ψ₀.lTensor k x) = ψ₁.lTensor k (a₀.lTensor k x) := by
    have h := congrArg (LinearMap.lTensor k) h2
    rw [LinearMap.lTensor_comp, LinearMap.lTensor_comp] at h
    exact (LinearMap.congr_fun h x).symm
  have hv : d0 F' (th0 m (ψ₀.lTensor k x)) = 0 := by
    rw [← comparison_degree_one_tensor_coboundary, hx1, hx, map_zero, map_zero]
  obtain ⟨c, hc⟩ := (hS.1 _).1 hv
  have hone : c0 m (1 : C0 F) = 1 := funext fun T ↦ map_one (m.α T)
  have hce : th0 m (ψ₀.lTensor k (c • ((1 : k) ⊗ₜ[R] e))) = th0 m (ψ₀.lTensor k x) := by
    rw [← hc, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one, LinearMap.lTensor_tmul, he, th0,
      liftSemi_tmul, hone, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one]
  have hψ : ψ₀.lTensor k (x - c • ((1 : k) ⊗ₜ[R] e)) = 0 := by
    rw [map_sub, hb.1 hce, sub_self]
  have ha' : a₀.lTensor k (x - c • ((1 : k) ⊗ₜ[R] e)) = 0 := by
    rw [map_sub, hx, TensorProduct.smul_tmul', LinearMap.lTensor_tmul, ha, TensorProduct.tmul_zero,
      sub_zero]
  obtain ⟨y, hy⟩ := (hQ (ModuleCat.of R k)).1.1 _ ha' ⟨0, by rw [map_zero]; exact hψ.symm⟩
  refine ⟨c, sub_eq_zero.1 ?_⟩
  rw [← hy]
  rfl

end GlobalTheory.CompanionTheory.PerfVB
