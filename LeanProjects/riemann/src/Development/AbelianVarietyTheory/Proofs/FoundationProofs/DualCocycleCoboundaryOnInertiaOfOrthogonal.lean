import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DvdOfMemIk
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductFixedSubmoduleRestrictDual

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

namespace GlobalTheory.Ord2.GwIneq

theorem cob_of_perp_transport {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    {Γ D : Type} [Group Γ] [Group D] [TopologicalSpace D]
    {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    (μ : Γ →* Rˣ) (rho : Representation R Γ M) (φ : D →* Γ) (J : Subgroup D)
    (h : ContAction (rho.comp φ)) (h' : ContAction ((rho.comp φ).comp (MonoidHom.id D)))
    (key : ∀ y : H1 (twDual (μ.comp φ) (rho.comp φ)),
      (∀ x ∈ H1ur (rho.comp φ) J, cupH1H1TwistedDual (μ.comp φ) (rho.comp φ) (MonoidHom.id D) h' y x = 0) →
        y ∈ H1ur (twDual (μ.comp φ) (rho.comp φ)) J)
    (f : Z1 ((twDual μ rho).comp φ))
    (hf : ∀ a ∈ H1ur (rho.comp φ) J, cupH1H1TwistedDual μ rho φ h (Submodule.mkQ _ f) a = 0) :
    ∃ m : TDual R M, ∀ s ∈ J, f.1 s = twDual μ rho (φ s) m - m := by
  have heq : twDual (μ.comp φ) (rho.comp φ) = (twDual μ rho).comp φ := by
    refine MonoidHom.ext fun s => LinearMap.ext fun ψ => TDual.ext fun x => ?_
    simp only [MonoidHom.comp_apply, twDual_apply, map_inv φ]
  have hf' : f.1 ∈ Z1 (twDual (μ.comp φ) (rho.comp φ)) := by rw [heq]; exact f.2
  have hy := key (Submodule.Quotient.mk ⟨f.1, hf'⟩) (by
    intro x hx
    induction x using Submodule.Quotient.induction_on with | H a =>
    have e := hf _ hx
    have e' := (Submodule.Quotient.mk_eq_zero _).1 e
    exact (Submodule.Quotient.mk_eq_zero _).2 e')
  rw [H1ur, LinearMap.mem_ker] at hy
  change Submodule.Quotient.mk (restrictCocycles1 _ J.subtype continuous_subtype_val ⟨f.1, hf'⟩) = 0 at hy
  rw [Submodule.Quotient.mk_eq_zero] at hy
  obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hy
  refine ⟨m, fun s hs => ?_⟩
  have e := hm ⟨s, hs⟩
  change f.1 s = twDual (μ.comp φ) (rho.comp φ) s m - m at e
  rw [e, heq]
  rfl

theorem dual_cocycle_cob_on_inertia : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ), 1 ≤ n → ∀ (S : Finset Pl) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ n)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation (ZMod (l ^ n)) (GS Ω (S : Set Pl)) M) (hrho : ContAction rho) (μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ), μ.comp (toGS Ω (S : Set Pl)) = cycMod ℚ Ω l n → ∀ (B : ValuationSubring Ω) (q : Pl), IsPlaceOver B q → ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ f : Z1 ((twDual μ rho).comp (locHom (S : Set Pl) B)), (∀ a ∈ H1ur (rho.comp (locHom (S : Set Pl) B)) ((Ine (F := ℚ) B).subgroupOf (Dec (F := ℚ) B)), cupH1H1TwistedDual μ rho (locHom (S : Set Pl) B) (hrho.comp' (continuous_locHom _ B)) (Submodule.mkQ _ f) a = 0) → ∃ m : TDual (ZMod (l ^ n)) M, ∀ s : Dec (F := ℚ) B, (s : G ℚ Ω) ∈ Ine (F := ℚ) B → f.1 s = twDual μ rho (locHom (S : Set Pl) B s) m - m := by
  intro hL l _ Ω _ _ _ n hn S M _ _ _ _ _ rho hrho μ hμ B q hq hl f hf
  have hχ : (cycMod ℚ Ω l n).comp (Dec (F := ℚ) B).subtype = μ.comp (locHom (S : Set Pl) B) := by
    rw [← hμ]; rfl
  have hc := hrho.comp' (continuous_locHom (S : Set Pl) B)
  have key := GlobalTheory.Ord2.unramified_h1_dual_iff_perp hL ℚ Ω l n M B q (rho.comp (locHom (S : Set Pl) B)) hc
    hq hn hl
  rw [hχ] at key
  obtain ⟨m, hm⟩ := cob_of_perp_transport μ rho (locHom (S : Set Pl) B) _ hc _
    (fun y hy => (key y).2 hy) f hf
  exact ⟨m, fun s hs => hm s (Subgroup.mem_subgroupOf.2 hs)⟩

end GlobalTheory.Ord2.GwIneq
