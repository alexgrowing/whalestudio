import Mathlib

namespace GlobalTheory.LocFinIso

def subK {G : Type} [Group G] (K : Set G) (h1 : (1 : G) ∈ K)
    (hmul : ∀ k ∈ K, ∀ k' ∈ K, k * k' ∈ K) : Submonoid G where
  carrier := K
  one_mem' := h1
  mul_mem' := fun {a b} ha hb => hmul a ha b hb

def repD {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : G →* Module.End ℂ V) (D : Submodule ℂ V) (K : Set G) (h1 : (1 : G) ∈ K)
    (hmul : ∀ k ∈ K, ∀ k' ∈ K, k * k' ∈ K) (hst : ∀ k ∈ K, ∀ x ∈ D, ρ k x ∈ D) :
    Representation ℂ (subK K h1 hmul) D where
  toFun k := (ρ k).restrict (fun x hx => hst k k.2 x hx)
  map_one' := by ext x; simp [LinearMap.restrict_apply]
  map_mul' := fun a b => by ext x; simp [LinearMap.restrict_apply, Module.End.mul_apply]

theorem repD_apply {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : G →* Module.End ℂ V) (D : Submodule ℂ V) (K : Set G) (h1 : (1 : G) ∈ K)
    (hmul : ∀ k ∈ K, ∀ k' ∈ K, k * k' ∈ K) (hst : ∀ k ∈ K, ∀ x ∈ D, ρ k x ∈ D)
    (k : subK K h1 hmul) (x : D) : ((repD ρ D K h1 hmul hst k x : D) : V) = ρ k x := rfl

noncomputable def leftMul {G : Type} {m : ℕ} (A : G → Matrix (Fin m) (Fin m) ℂ) (g : G) :
    EuclideanSpace ℂ (Fin (m * m)) →L[ℂ] EuclideanSpace ℂ (Fin (m * m)) :=
  Matrix.toEuclideanCLM (n := Fin (m * m)) (𝕜 := ℂ) (Matrix.reindex finProdFinEquiv finProdFinEquiv
    (Matrix.kroneckerMap (· * ·) (A g) (1 : Matrix (Fin m) (Fin m) ℂ)))

section
variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : G →* Module.End ℂ V) (D : Submodule ℂ V) (K : Set G) (h1 : (1 : G) ∈ K)
    (hmul : ∀ k ∈ K, ∀ k' ∈ K, k * k' ∈ K) (hst : ∀ k ∈ K, ∀ x ∈ D, ρ k x ∈ D)

theorem smul_val (a : MonoidAlgebra ℂ (subK K h1 hmul)) (u : (repD ρ D K h1 hmul hst).asModule) :
    (((repD ρ D K h1 hmul hst).asModuleEquiv (a • u) : D) : V) =
      ∑ κ ∈ a.coeff.support, a.coeff κ • ρ κ (((repD ρ D K h1 hmul hst).asModuleEquiv u : D) : V) := by
  rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply]
  simp [Finsupp.sum, repD_apply]

noncomputable def toEndD
    (g : (repD ρ D K h1 hmul hst).asModule →ₗ[MonoidAlgebra ℂ (subK K h1 hmul)]
      (repD ρ D K h1 hmul hst).asModule) : D →ₗ[ℂ] D where
  toFun u := (repD ρ D K h1 hmul hst).asModuleEquiv (g ((repD ρ D K h1 hmul hst).asModuleEquiv.symm u))
  map_add' u v := by simp
  map_smul' c u := by
    rw [Representation.asModuleEquiv_symm_map_smul, g.map_smul, Representation.asModuleEquiv_map_smul]
    simp

theorem toEndD_apply
    (g : (repD ρ D K h1 hmul hst).asModule →ₗ[MonoidAlgebra ℂ (subK K h1 hmul)]
      (repD ρ D K h1 hmul hst).asModule) (u : D) :
    toEndD ρ D K h1 hmul hst g u =
      (repD ρ D K h1 hmul hst).asModuleEquiv (g ((repD ρ D K h1 hmul hst).asModuleEquiv.symm u)) := rfl

end

end GlobalTheory.LocFinIso
