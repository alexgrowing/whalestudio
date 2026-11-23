import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLatFlagPair
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num

section General

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {V : Type} [AddCommGroup V]
  [Module Ω V]

theorem patch_eq_of_subset {S₀ S : Finset ℕ} (h : S₀ ⊆ S) (L₀ : Lat ξ V) (Lp : ℕ → Lat ξ V) {q : Cpt ξ}
    (hq : ∀ p ∈ S, p ∉ S₀ → ¬ InFibre ξ p q) : Lat.patch S₀ L₀ Lp q = Lat.patch S L₀ Lp q := by
  have hmem : ∀ p, (p ∈ S₀ ∧ InFibre ξ p q) ↔ (p ∈ S ∧ InFibre ξ p q) := fun p =>
    ⟨fun ⟨a, b⟩ => ⟨h a, b⟩, fun ⟨a, b⟩ => ⟨by_contra fun c => hq p a c b, b⟩⟩
  have hex : (∃ p ∈ S₀, InFibre ξ p q) ↔ ∃ p ∈ S, InFibre ξ p q := exists_congr hmem
  simp only [Lat.patch]
  by_cases hc : ∃ p ∈ S, InFibre ξ p q
  · rw [if_pos hc, if_pos (hex.2 hc)]
    refine le_antisymm (le_iInf₂ fun p hp => le_iInf fun hf => ?_) (le_iInf₂ fun p hp => le_iInf fun hf => ?_)
    · exact iInf₂_le_of_le p ((hmem p).2 ⟨hp, hf⟩).1 (iInf_le _ hf)
    · exact iInf₂_le_of_le p (h hp) (iInf_le _ hf)
  · rw [if_neg hc, if_neg (fun c => hc (hex.1 c))]

theorem gr_congr_at {L L' : Lat ξ V} {r : ℕ} (b : Fin r → V) (i : Fin r) {q : Cpt ξ} (hq : L q = L' q) :
    L.gr b i q = L'.gr b i q := by
  simp only [Lat.gr, hq]

theorem tens_congr_at {I : Type} [Fintype I] {Λ Λ' : I → Lat ξ Ω} (a : I → ℤ) {q : Cpt ξ}
    (hq : ∀ i, Λ i q = Λ' i q) : Lat.tens Λ a q = Lat.tens Λ' a q := by
  simp only [Lat.tens, Lat.IsGenAt, hq]

end General

theorem rootLat_shrink_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (Fl : 𝔐.Flag) (S₀ : Finset ℕ) (h : S₀ ⊆ S) (hvb : ∀ s, (𝔐.VAt S₀ s).IsVB (labelRk D s) (𝔐.Vgen s)) (hsub : ∀ s, (𝔐.VAt S₀ s).IsFlagVBOn Set.univ (Fl.b s)) (q : Cpt 𝔐.ξ), (∀ p ∈ S, p ∉ S₀ → ¬ InFibre 𝔐.ξ p q) → ∀ r, (Fl.shrink S₀ h hvb hsub).rootLat r q = Fl.rootLat r q := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d _ Fl S₀ h hvb hsub q hq r
  refine tens_congr_at (Λ := fun _ : Unit => (𝔐.VAt S₀ (HodgeCpt.rootIdx D r).1).gr (Fl.b (HodgeCpt.rootIdx D r).1)
    (HodgeCpt.rootIdx D r).2) (Λ' := fun _ : Unit => (𝔐.V (HodgeCpt.rootIdx D r).1).gr (Fl.b (HodgeCpt.rootIdx D r).1)
    (HodgeCpt.rootIdx D r).2) _ fun _ => gr_congr_at _ _ ?_
  exact patch_eq_of_subset h _ _ hq

end GlobalTheory.CompanionTheory.Ar.Num

end
