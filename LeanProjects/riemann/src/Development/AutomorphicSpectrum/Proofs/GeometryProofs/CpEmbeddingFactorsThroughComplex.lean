import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem exists_emb_through_coeff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (p : Nat.Primes)
    (κ : c.F →+* ℂ_[p]) (s : E →+* ℂ_[p]), ∃ τ : E →+* ℂ, s = κ.comp (inE c τ) := by
  intro E _ _ _ H l c p κ s
  haveI : CharZero ℂ_[p] := charZero_of_injective_ringHom κ.injective
  have hinj : Function.Injective (fun τ : E →+* ℂ => κ.comp (inE c τ)) := by
    intro τ τ' h
    ext a
    have h1 : κ (inE c τ a) = κ (inE c τ' a) := RingHom.congr_fun h a
    have h2 := κ.injective h1
    exact congrArg (fun x : c.F => (x : ℂ)) h2
  have hle : Nat.card (E →+* ℂ_[p]) ≤ Nat.card (E →+* ℂ) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, NumberField.Embeddings.card E ℂ,
      NumberField.Embeddings.card E ℂ_[p]]
  haveI : Finite (E →+* ℂ_[p]) := inferInstance
  obtain ⟨τ, hτ⟩ := (hinj.bijective_of_nat_card_le hle).2 s
  exact ⟨τ, hτ.symm⟩

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
