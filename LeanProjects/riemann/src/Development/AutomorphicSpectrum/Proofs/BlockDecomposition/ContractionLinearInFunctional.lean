import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

theorem con_add_form {R : Type} [CommRing R] {I : Type} [Finite I] (V : I → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module R (V i)] (M : Type) [AddCommGroup M] [Module R M] (Ξ Ξ' : (∀ i, V i) →ₗ[R] R)
    (u : ∀ i, V i ⊗[R] M) : con V M (Ξ + Ξ') u = con V M Ξ u + con V M Ξ' u := by
  refine GlobalTheory.CompanionTheory.HopfC.pure_induction V M
    (P := fun u => GlobalTheory.CompanionTheory.HopfC.con V M (Ξ + Ξ') u = GlobalTheory.CompanionTheory.HopfC.con V M Ξ u + GlobalTheory.CompanionTheory.HopfC.con V M Ξ' u)
    ?_ ?_ ?_ u
  · simp only [map_zero, add_zero]
  · intro f m
    simp only [GlobalTheory.CompanionTheory.HopfC.con_pure, LinearMap.add_apply, add_smul]
  · intro u v hu hv
    rw [map_add, map_add, map_add, hu, hv]
    abel

theorem con_smul_form {R : Type} [CommRing R] {I : Type} [Finite I] (V : I → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module R (V i)] (M : Type) [AddCommGroup M] [Module R M] (r : R) (Ξ : (∀ i, V i) →ₗ[R] R)
    (u : ∀ i, V i ⊗[R] M) : con V M (r • Ξ) u = r • con V M Ξ u := by
  refine GlobalTheory.CompanionTheory.HopfC.pure_induction V M
    (P := fun u => GlobalTheory.CompanionTheory.HopfC.con V M (r • Ξ) u = r • GlobalTheory.CompanionTheory.HopfC.con V M Ξ u)
    ?_ ?_ ?_ u
  · simp only [map_zero, smul_zero]
  · intro f m
    simp only [GlobalTheory.CompanionTheory.HopfC.con_pure, LinearMap.smul_apply, smul_eq_mul, mul_smul]
  · intro u v hu hv
    rw [map_add, map_add, hu, hv, smul_add]

theorem Con_linear_form {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {p q : ℕ}
    [Finite (Fin (p + 1) ⥤ C)] (Ξ Ξ' : Cn F p →ₗ[R] R) (r : R) (B : Bi F p q) :
    Con F (Ξ + Ξ') q B = Con F Ξ q B + Con F Ξ' q B ∧ Con F (r • Ξ) q B = r • Con F Ξ q B := by
  have key : ∀ (Θ : MainStatements.Hodge.Cn F p →ₗ[R] R) (b : Fin (q + 1) ⥤ C),
      GlobalTheory.CompanionTheory.HopfC.Con F Θ q B b =
        GlobalTheory.CompanionTheory.HopfC.con (fun a : Fin (p + 1) ⥤ C => (F.obj (a.obj (Fin.last p)) : Type))
          (F.obj (b.obj (Fin.last q)) : Type) Θ (fun a => B a b) := fun _ _ => rfl
  refine ⟨funext fun b => ?_, funext fun b => ?_⟩
  · rw [key, GlobalTheory.CompanionTheory.HopfC.con_add_form]
    rfl
  · rw [key, GlobalTheory.CompanionTheory.HopfC.con_smul_form]
    rfl

end GlobalTheory.CompanionTheory.HopfC
