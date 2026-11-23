import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsOfCmTriplePullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem pat_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (T : PAT H (Sp R)), (∃ (T' : PAT H (Sp R')) (_ : SABMap T'.t T.t (spMap f)), T'.g = T.g) ∧ ∀ (T' : PAT H (Sp R')) (m : SABMap T'.t T.t (spMap f)), Nontrivial R' → T'.g = T.g ∧ IsPolFibre f T.pol T'.pol m.φ ∧ ∃ w : LB.Iso T'.t.PP.L (T.t.PP.L.pull m.φ), RigIso m w := by
  intro E _ _ _ H R R' _ _ f T
  refine ⟨?_, fun T' m hR => ?_⟩
  · obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap f) T.t
    obtain ⟨⟨T', ht, hg⟩, -⟩ := PAT.exists_of_sabMap E H _ _ _ T _ m
    exact ⟨T', ht ▸ m, hg⟩
  · obtain ⟨-, e⟩ := PAT.exists_of_sabMap E H _ _ _ T _ m
    have hd : SmoothOfRelativeDimension T.g T'.t.G.hom :=
      have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} T.g
      MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension T.g) m.cart.1 T.dim
    obtain ⟨p⟩ : Nonempty (PrimeSpectrum R') := inferInstance
    have hg : T'.g = T.g := ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ T'.dim hd (eSec T'.t.G p)
    obtain ⟨w, hw, hr, -⟩ := m.lin
    exact ⟨hg, ⟨hg, m.cart, e⟩, w, hw, hr⟩

end GlobalTheory.LamT
