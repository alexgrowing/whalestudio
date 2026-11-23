import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory

theorem sabMap_cancel_and_comp_over : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S₁ S₂ : Scheme.{0}) (t : SAB H S) (t₁ : SAB H S₁) (t₂ : SAB H S₂) (f₁ : S₁ ⟶ S) (f₂ : S₂ ⟶ S) (g : S₂ ⟶ S₁) (m₁ : SABMap t₁ t f₁) (m₂ : SABMap t₂ t f₂), f₂ = g ≫ f₁ → (∃ n : SABMap t₂ t₁ g, n.φ ≫ m₁.φ = m₂.φ) ∧ ∀ n : SABMap t₂ t₁ g, ∃ m : SABMap t₂ t f₂, m.φ = n.φ ≫ m₁.φ := by
  intro E _ _ _ H S S₁ S₂ t t₁ t₂ f₁ f₂ g m₁ m₂ h
  subst h
  obtain ⟨n, hn⟩ := sabCancel pullCubCancel E H _ _ _ t t₁ t₂ f₁ g m₁ m₂
  exact ⟨⟨n, hn.symm⟩, fun n => sabComp pullCubComp E H _ _ _ t t₁ t₂ f₁ g m₁ n⟩

end GlobalTheory
