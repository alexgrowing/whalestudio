import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.localizationAway_glue_of_forall_prime : ∀ (B : Type) [CommRing B] (s : Set B), (∀ P : PrimeSpectrum B, ∃ f ∈ s, f ∉ P.asIdeal) → ∀ v : ∀ f : s, Localization.Away (f : B), (∀ (f g : s) (D : Type) [CommRing D] [Algebra B D] (α : Localization.Away (f : B) →ₐ[B] D) (β : Localization.Away (g : B) →ₐ[B] D), α (v f) = β (v g)) → ∃ b : B, ∀ f : s, algebraMap B (Localization.Away (f : B)) b = v f := by
  intro B _ s hs v hv
  have span_eq : Ideal.span s = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hsM⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨f, hf, hfM⟩ := hs ⟨M, hM.isPrime⟩
    exact hfM (hsM (Ideal.subset_span hf))
  obtain ⟨r, hr, -⟩ := Localization.existsUnique_algebraMap_eq_of_span_eq_top s span_eq v
    (fun a b => by
      let α : Localization.Away (a : B) →ₐ[B] Localization.Away ((a : B) * b) :=
        { IsLocalization.Away.awayToAwayRight (P := Localization.Away ((a : B) * b)) (a : B) (b : B) with
          commutes' := fun z => IsLocalization.Away.awayToAwayRight_eq _ _ _ }
      let β : Localization.Away (b : B) →ₐ[B] Localization.Away ((a : B) * b) :=
        { IsLocalization.Away.awayToAwayLeft (P := Localization.Away ((a : B) * b)) (b : B) (a : B) with
          commutes' := fun z => IsLocalization.Away.awayToAwayLeft_eq _ _ _ }
      exact hv a b _ α β)
  exact ⟨r, hr⟩
