import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibOrd

section twEquiv
variable {G M V W : Type} [Group G] [Group M] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem nonempty_twAct_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ)
    (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n) :
    Nonempty ((twAct ρ N θ s hs).Equiv (twAct σ N θ s hs)) := by
  have he : ∀ v, e.toLinearEquiv v = e v := fun v => rfl
  have hl : ∀ v, e.toIntertwiningMap.toLinearMap v = e v := fun v => rfl
  have hmap : (GlobalTheory.PRep.twKer ρ N θ).map (e.toLinearEquiv : V →ₗ[ℂ] W) = GlobalTheory.PRep.twKer σ N θ := by
    unfold GlobalTheory.PRep.twKer
    rw [Submodule.map_span]
    congr 1
    ext w
    constructor
    · rintro ⟨x, ⟨n, v, rfl⟩, rfl⟩
      refine ⟨n, e v, ?_⟩
      simp only [LinearEquiv.coe_coe, map_sub, map_smul, he, hl, eint]
    · rintro ⟨n, w', rfl⟩
      refine ⟨ρ n (e.toLinearEquiv.symm w') - ((θ n : ℂˣ) : ℂ) • e.toLinearEquiv.symm w', ⟨n, _, rfl⟩, ?_⟩
      have hw : e (e.toLinearEquiv.symm w') = w' := e.toLinearEquiv.apply_symm_apply w'
      simp only [LinearEquiv.coe_coe, map_sub, map_smul, he, hl, eint, hw]
  refine ⟨Representation.Equiv.mk (Submodule.Quotient.equiv _ _ e.toLinearEquiv hmap) fun m => ?_⟩
  apply Submodule.linearMap_qext
  ext v
  exact congrArg (Submodule.Quotient.mk (p := GlobalTheory.PRep.twKer σ N θ)) (eint e (s m) v)

theorem nonempty_twist_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) (χ : G →* ℂˣ) :
    Nonempty ((twist ρ χ).Equiv (twist σ χ)) := by
  have he : ∀ v, e.toLinearEquiv v = e v := fun v => rfl
  refine ⟨Representation.Equiv.mk e.toLinearEquiv fun g => LinearMap.ext fun v => ?_⟩
  show e.toLinearEquiv (((χ g : ℂˣ) : ℂ) • ρ g v) = ((χ g : ℂˣ) : ℂ) • σ g (e.toLinearEquiv v)
  rw [map_smul, he, he, eint]

end twEquiv

theorem miso_phiN (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle) (n : ℕ) (A B : MRep k (n + 1)) (h : MIso A B) : MIso (phiN ψ A) (phiN ψ B) := by
  have h1 : MIso (GlobalTheory.BZMir.MRep.phiM k ψ A) (GlobalTheory.BZMir.MRep.phiM k ψ B) := by
    obtain ⟨e⟩ := h
    unfold GlobalTheory.BZMir.MRep.phiM GlobalTheory.BZMir.phiMinus
    generalize_proofs hh
    exact nonempty_twAct_equiv e _ _ _ hh
  obtain ⟨e'⟩ := h1
  exact nonempty_twist_equiv e' _

end GlobalTheory.CompanionTheory.LeibOrd

end
