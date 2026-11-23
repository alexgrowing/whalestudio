import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilGroupIsSemisimpleOfSemisimpleFrob

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

theorem exists_wdRep_pull_finite_twist :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
      (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (G : Type)
      [Group G] [Finite G] (π : Weil h →* G),
      IsOpen {σ : Ine (F := E) A | π (ineIncl h σ) = 1} → ∀ (n : ℕ)
      (R : Representation ℂ G (Fin n → ℂ)) (μ : Weil h →* ℂˣ), IsSmooth μ →
      ∃ b : WDRep h (Fin n → ℂ), ∀ σ, b.ρ σ = (μ σ : ℂ) • R (π σ) := by
  intro E Ω _ _ _ _ _ A w h G _ _ π hπ n R μ hμ
  have hsm : IsSmooth (R.comp π) :=
    IsSmooth.of_le (f := π) hπ fun σ hσ => by simp [hσ]
  have hss : ∀ σ, Module.End.IsSemisimple ((R.comp π) σ) := by
    intro σ
    have hu : IsUnit ((R.comp π) σ) := ((R.comp π).toHomUnits σ).isUnit
    refine FrobSemisimple.isSemisimple_of_pow hu (m := Nat.card G) Nat.card_pos ?_
    rw [← map_pow, MonoidHom.comp_apply, map_pow, pow_card_eq_one', map_one]
    exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero (p := Polynomial.X - Polynomial.C 1)
      (Polynomial.irreducible_X_sub_C 1).squarefree (by simp)
  let b0 : WDRep h (Fin n → ℂ) :=
    { ρ := R.comp π
      N := 0
      smooth := hsm
      semisimple := hss
      nilpotent := IsNilpotent.zero
      comm := fun σ => by simp }
  exact ⟨b0.twist μ hμ, fun σ => rfl⟩

end GlobalTheory.WeilDeligne
