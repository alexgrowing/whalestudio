import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC.ConMul

theorem con_mul_left {I : Type} [Finite I] {R : Type} [CommRing R] (V : I → Type) [∀ i, CommRing (V i)]
    [∀ i, Algebra R (V i)] (M : Type) [CommRing M] [Algebra R M] (Ξ : (∀ i, V i) →ₗ[R] R) (x : ∀ i, V i)
    (u : ∀ i, V i ⊗[R] M) :
    con V M Ξ (fun i ↦ (x i ⊗ₜ[R] (1 : M)) * u i) = con V M (Ξ ∘ₗ LinearMap.mulLeft R x) u := by
  revert u
  refine GlobalTheory.CompanionTheory.HopfC.pure_induction V M ?_ ?_ ?_
  · have h : (fun i ↦ (x i ⊗ₜ[R] (1 : M)) * (0 : ∀ i, V i ⊗[R] M) i) = 0 := by
      funext i
      simp
    rw [h, map_zero, map_zero]
  · intro f m
    have h : (fun i ↦ (x i ⊗ₜ[R] (1 : M)) * (f i ⊗ₜ[R] m)) = fun i ↦ (x * f) i ⊗ₜ[R] m := by
      funext i
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [h, GlobalTheory.CompanionTheory.HopfC.con_pure, GlobalTheory.CompanionTheory.HopfC.con_pure]
    rfl
  · intro u v hu hv
    have h : (fun i ↦ (x i ⊗ₜ[R] (1 : M)) * (u + v) i) =
        (fun i ↦ (x i ⊗ₜ[R] (1 : M)) * u i) + fun i ↦ (x i ⊗ₜ[R] (1 : M)) * v i := by
      funext i
      simp [mul_add]
    rw [h, map_add, map_add, hu, hv]

theorem con_mul_right {I : Type} [Finite I] {R : Type} [CommRing R] (V : I → Type) [∀ i, CommRing (V i)]
    [∀ i, Algebra R (V i)] (M : Type) [CommRing M] [Algebra R M] (Ξ : (∀ i, V i) →ₗ[R] R) (y : M)
    (u : ∀ i, V i ⊗[R] M) :
    con V M Ξ (fun i ↦ ((1 : V i) ⊗ₜ[R] y) * u i) = y * con V M Ξ u := by
  induction u using pure_induction with
  | h0 =>
    have h : (fun i ↦ ((1 : V i) ⊗ₜ[R] y) * (0 : ∀ i, V i ⊗[R] M) i) = 0 := by
      funext i; simp
    rw [h, map_zero, mul_zero]
  | hp f m =>
    have h : (fun i ↦ ((1 : V i) ⊗ₜ[R] y) * (f i ⊗ₜ[R] m)) = fun i ↦ f i ⊗ₜ[R] (y * m) := by
      funext i; simp
    rw [h, con_pure, con_pure, mul_smul_comm]
  | ha u v hu hv =>
    have h : (fun i ↦ ((1 : V i) ⊗ₜ[R] y) * (u + v) i) =
        (fun i ↦ ((1 : V i) ⊗ₜ[R] y) * u i) + (fun i ↦ ((1 : V i) ⊗ₜ[R] y) * v i) := by
      funext i; simp [mul_add]
    rw [h, map_add, map_add, hu, hv, mul_add]

theorem con_products {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {p q : ℕ}
    [Finite (Fin (p + 1) ⥤ C)] (Ξ : Cn F p →ₗ[R] R) (x : Cn F p) (y : Cn F q) (B : Bi F p q) :
    Con F Ξ q ((fun a _ ↦ x a ⊗ₜ[R] 1 : Bi F p q) * B) = Con F (Ξ ∘ₗ LinearMap.mulLeft R x) q B ∧
    Con F Ξ q ((fun _ b ↦ 1 ⊗ₜ[R] y b : Bi F p q) * B) = y * Con F Ξ q B ∧
    Con F Ξ q (1 : Bi F p q) = Ξ 1 • (1 : Cn F q) := by
  refine ⟨?_, ?_, ?_⟩
  · funext b
    exact GlobalTheory.CompanionTheory.HopfC.ConMul.con_mul_left (fun a : Fin (p + 1) ⥤ C ↦ F.obj (a.obj (Fin.last p)))
      (F.obj (b.obj (Fin.last q))) Ξ x (fun a ↦ B a b)
  · funext b
    exact GlobalTheory.CompanionTheory.HopfC.ConMul.con_mul_right (fun a : Fin (p + 1) ⥤ C ↦ F.obj (a.obj (Fin.last p)))
      (F.obj (b.obj (Fin.last q))) Ξ (y b) (fun a ↦ B a b)
  · funext b
    exact GlobalTheory.CompanionTheory.HopfC.con_pure (fun a : Fin (p + 1) ⥤ C ↦ F.obj (a.obj (Fin.last p)))
      (F.obj (b.obj (Fin.last q))) Ξ 1 1

end GlobalTheory.CompanionTheory.HopfC.ConMul
