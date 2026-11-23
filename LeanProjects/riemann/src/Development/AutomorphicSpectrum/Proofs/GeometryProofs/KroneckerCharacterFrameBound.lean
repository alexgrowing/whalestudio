import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBareNormDisc
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatFirstFromResolutionAndGagaStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatDegreeHoldsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KroneckerCharacterPeriodFormula
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyUniformizationTypeRelayStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

namespace GlobalTheory.CompanionTheory.Ar.Br

theorem degree_of_flatOnModel : Geo.ResK.ResKStatement → GagaSections → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [NumberField c.F] (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (φ : FrameFn Xo c) (N : LogNorms c.F) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → FracBase β → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → IsClopen U → Z.IsGeom → FlatOnModel Z τ φ → (∀ s, HasInfNorm U τ φ s (N.inf s)) → (∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), HasFinNorm U τ φ p κ (N.fin p κ)) → N.IsAdelic ∧ N.deg = ((D.p : ℝ) - D.q) / 2 * (GlobalTheory.CM.logOm E χ).re := by
  intro hres hgaga E _ _ _ H D l Xo c O _ β Y _ U Z τ φ N _ χ hχ hO hpq hτ hcl hZ hflat hinf hfin
  obtain ⟨g, ty, FU, i, hty, hin⟩ := GlobalTheory.T.family_uniformization_type_relay E H D l Xo c U hpq hcl ⟨_, Z.genPt_mem⟩
  have hA := GlobalTheory.T.flat_first_from_resolution_and_gaga hres hgaga E H D l Xo c O β Y U Z τ φ hO hpq hτ hZ hflat.isLineFn hflat
  exact GlobalTheory.CompanionTheory.Ar.Fl.TopLL.degree_frames GlobalTheory.T.FlatDegree_holds E H D l Xo c g ty FU i U τ φ N χ hχ hty hτ
    (hA.2 g ty FU i hty hin) hinf hfin

end GlobalTheory.CompanionTheory.Ar.Br
