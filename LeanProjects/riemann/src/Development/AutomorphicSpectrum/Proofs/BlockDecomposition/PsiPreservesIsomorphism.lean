import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibOrd.PsiIso

private theorem mapQ_eq_id_of_eq_id {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (p : Submodule R M) {f : M →ₗ[R] M} (hf : f = LinearMap.id) (h : p ≤ p.comap f) :
    p.mapQ p f h = LinearMap.id := by
  subst hf
  exact Submodule.mapQ_id p h

private theorem mapQ_congr {R M M₂ : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M₂]
    [Module R M₂] (p : Submodule R M) (q : Submodule R M₂) {f g : M →ₗ[R] M₂} (hfg : f = g)
    (hf : p ≤ q.comap f) (hg : p ≤ q.comap g) : p.mapQ q f hf = p.mapQ q g hg := by
  subst hfg
  rfl

theorem twAct_equiv {G M V W : Type} [Group G] [Group M] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n) :
    Nonempty ((twAct ρ N θ s hs).Equiv (twAct σ N θ s hs)) := by
  let eL : V ≃ₗ[ℂ] W :=
    { e.toIntertwiningMap.toLinearMap with
      invFun := e.invFun
      left_inv := e.left_inv
      right_inv := e.right_inv }
  have hf : ∀ (g : G) (v : V), (eL : V →ₗ[ℂ] W) (ρ g v) = σ g ((eL : V →ₗ[ℂ] W) v) :=
    fun g v => Representation.IntertwiningMap.isIntertwining ρ σ e.toIntertwiningMap g v
  have hg : ∀ (g : G) (w : W), (eL.symm : W →ₗ[ℂ] V) (σ g w) = ρ g ((eL.symm : W →ₗ[ℂ] V) w) := by
    intro g w
    apply eL.injective
    have := hf g (eL.symm w)
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this ⊢
    exact this.symm
  have hf' : ∀ (g : G) (v : V), eL (ρ g v) = σ g (eL v) := hf
  have hfc : ∀ g : G, (eL : V →ₗ[ℂ] W) ∘ₗ ρ g = σ g ∘ₗ (eL : V →ₗ[ℂ] W) :=
    fun g => LinearMap.ext fun v => hf g v
  let F := GlobalTheory.BZMir.twMap ρ σ N θ (eL : V →ₗ[ℂ] W) hf
  let F' := GlobalTheory.BZMir.twMap σ ρ N θ (eL.symm : W →ₗ[ℂ] V) hg
  have hF'F : F' ∘ₗ F = LinearMap.id := by
    simp only [F, F', GlobalTheory.BZMir.twMap]
    rw [← Submodule.mapQ_comp]
    refine mapQ_eq_id_of_eq_id _ ?_ _
    ext v
    simp
  have hFF' : F ∘ₗ F' = LinearMap.id := by
    simp only [F, F', GlobalTheory.BZMir.twMap]
    rw [← Submodule.mapQ_comp]
    refine mapQ_eq_id_of_eq_id _ ?_ _
    ext w
    simp
  have hcomm : ∀ m : M, F ∘ₗ GlobalTheory.BZMir.twAct ρ N θ s hs m =
      GlobalTheory.BZMir.twAct σ N θ s hs m ∘ₗ F := by
    intro m
    first
      | (simp only [F, GlobalTheory.BZMir.twMap, GlobalTheory.BZMir.twAct,
            MonoidHom.coe_mk, OneHom.coe_mk]
         erw [← Submodule.mapQ_comp, ← Submodule.mapQ_comp]
         exact mapQ_congr _ _ (hfc (s m)) _ _)
      | (apply Submodule.linearMap_qext
         ext v
         simp [F, GlobalTheory.BZMir.twMap, GlobalTheory.BZMir.twAct, hf, hf'])
  exact ⟨⟨⟨F, hcomm⟩, F', fun x => LinearMap.congr_fun hF'F x, fun y => LinearMap.congr_fun hFF' y⟩⟩

theorem giso_psiN : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (A B : MRep k n), MIso A B → GIso (psiN A) (psiN B) := by
  intro k _ _ _ _ n A B ⟨e⟩
  exact GlobalTheory.CompanionTheory.LeibOrd.giso_tw _
    (GlobalTheory.CompanionTheory.LeibOrd.PsiIso.twAct_equiv e (GlobalTheory.BZMir.MirUin k n) 1
      (GlobalTheory.BZMir.levi k n) (GlobalTheory.BZMir.levi_normalises n))

end GlobalTheory.CompanionTheory.LeibOrd.PsiIso

end
