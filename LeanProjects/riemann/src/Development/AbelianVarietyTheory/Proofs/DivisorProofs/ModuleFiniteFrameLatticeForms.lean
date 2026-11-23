import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Formalism.PieriBlockIdeals.PieriColumnMinors.DepthNonnegative

set_option autoImplicit false

open GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.UG Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD

namespace GlobalTheory.ExpFrame

theorem finite_forms_of_classes {O : Type} [CommRing O] {W : Type} [AddCommGroup W] [Module O W] [IsNoetherian O W]
    {G : Type} [Group G] (Γ K : Subgroup G) (ρ : Representation O K W)
    (h : ∃ S : Finset G, ∀ g, ∃ γ ∈ Γ, ∃ s ∈ S, ∃ κ ∈ K, g = γ * s * κ) : Module.Finite O (AMFK O Γ K ρ) := by
  obtain ⟨S, hS⟩ := h
  let ev : AMFK O Γ K ρ →ₗ[O] (S → W) :=
    (LinearMap.funLeft O W (Subtype.val : S → G)).comp (AMFK O Γ K ρ).subtype
  refine Module.Finite.of_injective ev ?_
  intro f f' hff
  ext g
  obtain ⟨γ, hγ, s, hs, κ, hκ, rfl⟩ := hS g
  have h1 := f.2 ⟨γ, hγ⟩ s ⟨κ, hκ⟩
  have h2 := f'.2 ⟨γ, hγ⟩ s ⟨κ, hκ⟩
  have h3 : (f : G → W) s = (f' : G → W) s := congrFun hff ⟨s, hs⟩
  exact h1.trans ((congrArg _ h3).trans h2.symm)

theorem Frame.finite_latticeForms : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (mu : ι → ℕ → ℕ) (jK : F.K →* alg F.O N mu), F.Ok → Module.Finite F.O (Forms F.O (A := alg F.O N mu) F.Γ jK (NablaT F.O N mu)) := by
  intro l _ ι _ _ N F mu jK hF
  have : ∀ τ : ι, Module.Finite F.O (dualWeyl F.O N N (res N (mu τ))) :=
    fun τ => dualWeyl_module_finite F.O N N _
  have : IsNoetherian F.O (NablaT F.O N mu) := inferInstance
  exact finite_forms_of_classes F.Γ F.K _ hF.classes

end GlobalTheory.ExpFrame
