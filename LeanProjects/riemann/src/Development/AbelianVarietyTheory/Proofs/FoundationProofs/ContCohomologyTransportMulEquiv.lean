import Mathlib
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory

theorem dn_comp_monoidHom {R Γ Γ' M : Type*} [CommRing R] [Group Γ] [Group Γ'] [AddCommGroup M]
    [Module R M] (φ : Γ' →* Γ) (ρ : Representation R Γ M) (ρ' : Representation R Γ' M)
    (h : ∀ g m, ρ' g m = ρ (φ g) m) (n : ℕ) (f : (Fin n → Γ) → M) (g : Fin (n + 1) → Γ') :
    dn ρ' n (fun x => f (fun i => φ (x i))) g = dn ρ n f (fun i => φ (g i)) := by
  show ρ' (g 0) (f fun i => φ (g i.succ)) + (Finset.univ.sum fun j : Fin (n + 1) =>
      (-1 : R) ^ ((j : ℕ) + 1) • f (fun i => φ (Fin.contractNth j (· * ·) g i))) =
    ρ (φ (g 0)) (f fun i => φ (g i.succ)) + Finset.univ.sum fun j : Fin (n + 1) =>
      (-1 : R) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) fun i => φ (g i))
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  funext i
  simp only [Fin.contractNth]
  split_ifs <;> simp

theorem contCohomology_transport_mulEquiv :
    ∀ (R : Type) [CommRing R] (Γ Γ' : Type) [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ'] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (e : Γ' ≃* Γ), Continuous e → Continuous e.symm → ∀ (ρ : Representation R Γ M) (ρ' : Representation R Γ' M), (∀ g m, ρ' g m = ρ (e g) m) → Nonempty (H1 ρ ≃ H1 ρ') ∧ Nonempty (H2 ρ ≃ H2 ρ') ∧ (Subsingleton (Hn ρ 3) → Subsingleton (Hn ρ' 3)) := by
  intro R _ Γ Γ' _ _ _ _ M _ _ _ _ e he he' ρ ρ' h
  have h' : ∀ g m, ρ g m = ρ' (e.symm g) m := fun g m => by rw [h, e.apply_symm_apply]
  refine ⟨⟨⟨pairH1DecompositionMap ρ ρ' e.toMonoidHom he LinearMap.id continuous_id (fun g m => (h g m).symm),
      pairH1DecompositionMap ρ' ρ e.symm.toMonoidHom he' LinearMap.id continuous_id (fun g m => (h' g m).symm),
      ?_, ?_⟩⟩,
    ⟨⟨compatiblePairH2 ρ ρ' e.toMonoidHom he LinearMap.id continuous_id (fun g m => (h g m).symm),
      compatiblePairH2 ρ' ρ e.symm.toMonoidHom he' LinearMap.id continuous_id (fun g m => (h' g m).symm),
      ?_, ?_⟩⟩, ?_⟩
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H f =>
      refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => ?_))
      exact congrArg f.1 (e.apply_symm_apply g)
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H f =>
      refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => ?_))
      exact congrArg f.1 (e.symm_apply_apply g)
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H f =>
      refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => ?_))
      exact congrArg f.1 (Prod.ext (e.apply_symm_apply g.1) (e.apply_symm_apply g.2))
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H f =>
      refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => ?_))
      exact congrArg f.1 (Prod.ext (e.symm_apply_apply g.1) (e.symm_apply_apply g.2))
  · intro hs
    rw [GlobalTheory.Published.subsingleton_Hn_succ_iff] at hs ⊢
    intro f hf hd
    obtain ⟨c, hc, hcf⟩ := hs (fun x => f (fun i => e.symm (x i)))
      (hf.comp (continuous_pi fun i => he'.comp (continuous_apply i))) (by
        funext g
        have := dn_comp_monoidHom e.symm.toMonoidHom ρ' ρ h' 3 f g
        rw [hd] at this
        exact this)
    refine ⟨fun x => c (fun i => e (x i)),
      hc.comp (continuous_pi fun i => he.comp (continuous_apply i)), ?_⟩
    funext g
    have := dn_comp_monoidHom e.toMonoidHom ρ ρ' h 2 c g
    rw [hcf] at this
    refine this.trans ?_
    exact congrArg f (funext fun i => e.symm_apply_apply _)

end GlobalTheory
