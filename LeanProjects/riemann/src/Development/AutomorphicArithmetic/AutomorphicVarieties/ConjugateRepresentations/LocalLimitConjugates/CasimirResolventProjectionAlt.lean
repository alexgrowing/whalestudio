import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.AbsProj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.GardFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ClFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CommOfZalg
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasSym
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.GardSep
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem transport {G H M : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [AddCommGroup M] [Module ℂ M] (R : G →* (H →L[ℂ] H)) (f : M →ₗ[ℂ] H) (hf : Function.Injective f)
    (B : M →ₗ[ℂ] M) (ρ : G → M → M) (hR : ∀ g v, ‖R g v‖ = ‖v‖) (hρ : ∀ g m, f (ρ g m) = R g (f m))
    (hB : ∀ g m, B (ρ g m) = ρ g (B m)) (hs : ∀ m m', inner ℂ (f (B m)) (f m') = inner ℂ (f m) (f (B m')))
    (hW : ∀ W : Submodule ℂ H, GlobalTheory.AutomorphicL2Unitary.IsSubrep R W → (∀ m, f m ∈ W → f m = 0) → W = ⊥) :
    ∃ (P : H →L[ℂ] H) (Q S : ℕ → H →L[ℂ] H), (∀ g w, P (R g w) = R g (P w)) ∧ (∀ k g w, Q k (R g w) = R g (Q k w)) ∧
      (∀ k g w, S k (R g w) = R g (S k w)) ∧ (∀ k m, f m - Q k (f m) = S k (f (B m))) ∧
      (∀ w m, inner ℂ (P w) (f (B m)) = 0) ∧ ∀ w, Tendsto (fun k => Q k w) atTop (𝓝 (P w)) := by
  let ε : M ≃ₗ[ℂ] LinearMap.range f := LinearEquiv.ofInjective f hf
  let A : LinearMap.range f →ₗ[ℂ] LinearMap.range f := ε.toLinearMap ∘ₗ B ∘ₗ ε.symm.toLinearMap
  have hε : ∀ m, (ε m : H) = f m := fun _ => rfl
  have hA : ∀ m, (A (ε m) : H) = f (B m) := fun m => by
    simp only [A, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, hε]
  have hD : ∀ g, ∀ v ∈ LinearMap.range f, R g v ∈ LinearMap.range f := by
    rintro g _ ⟨m, rfl⟩
    exact ⟨ρ g m, hρ g m⟩
  obtain ⟨P, Q, S, h1, h2, h3, h4, h5, h6⟩ := absProj G H R (LinearMap.range f) A hD hR
    (by
      intro g v
      obtain ⟨m, rfl⟩ := ε.surjective v
      have : (⟨R g (ε m), hD g _ (ε m).2⟩ : LinearMap.range f) = ε (ρ g m) := Subtype.ext (hρ g m).symm
      rw [this, hA, hA, hB, hρ])
    (by
      intro v w
      obtain ⟨m, rfl⟩ := ε.surjective v
      obtain ⟨m', rfl⟩ := ε.surjective w
      rw [hA, hA, hε, hε, hs])
    (by
      intro W hs h
      refine hW W hs fun m hm => ?_
      have : f m ∈ W ⊓ LinearMap.range f := ⟨hm, m, rfl⟩
      rwa [h, Submodule.mem_bot] at this)
  refine ⟨P, Q, S, h1, h2, h3, fun k m => ?_, fun w m => ?_, h6⟩
  · rw [← hA]; exact h4 k (ε m)
  · rw [← hA]; exact h5 w (ε m)

theorem UpperTheory.V.Cj.H.casimir_resolvent_projection :
    UpperTheory.V.Cj.H.CasimirResolventProjection := by
  intro E _ _ _ a ha μ _ _ n e he c
  have hg := gardFacts E a ha μ
  obtain ⟨c1, c2, c3, -⟩ := clFacts E a μ
  obtain ⟨-, o2, o3⟩ := casOp E a n e he 0 c
  have hm : ∀ φ ∈ gard μ, casA 0 c e φ ∈ gard μ := (o3 (gard μ) fun X φ h => (hg φ h).2.2.2.1 X).1
  let f : gard μ →ₗ[ℂ] HL μ :=
    { toFun := fun φ => cl μ φ.1
      map_add' := fun φ ψ => by
        have := (c1 φ.1 ψ.1 1 1 (hg _ φ.2).2.1 (hg _ ψ.2).2.1).2
        simpa only [one_smul, Submodule.coe_add] using this
      map_smul' := fun s φ => by
        have := (c1 φ.1 φ.1 s 0 (hg _ φ.2).2.1 (hg _ φ.2).2.1).2
        simpa only [zero_smul, add_zero, Submodule.coe_smul, RingHom.id_apply] using this }
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro φ h
    exact Subtype.ext (c2 φ.1 (hg _ φ.2).1 (hg _ φ.2).2.1 h)
  obtain ⟨P, Q, S, h1, h2, h3, h4, h5, h6⟩ := transport (GlobalTheory.AutomorphicL2Unitary.R (latticeGL E a) μ) f hf
    ((casA 0 c e).restrict hm) (fun g φ => ⟨rt E a g φ.1, (hg _ φ.2).2.2.2.2 g⟩)
    (fun g v => GlobalTheory.AutomorphicL2Unitary.norm_R g v)
    (fun g φ => c3 φ.1 g (hg _ φ.2).2.1)
    (fun g φ => Subtype.ext (LinearMap.congr_fun (o2 g).eq φ.1).symm)
    (fun φ ψ => casSym E a ha μ n e c φ.1 φ.2 ψ.1 ψ.2)
    (fun W hW h => gardSep E a μ W hW fun φ hφ => h ⟨φ, hφ⟩)
  exact ⟨P, Q, S, h1, h2, h3, fun k φ hφ => h4 k ⟨φ, hφ⟩, fun F φ hφ => h5 F ⟨φ, hφ⟩, h6⟩
