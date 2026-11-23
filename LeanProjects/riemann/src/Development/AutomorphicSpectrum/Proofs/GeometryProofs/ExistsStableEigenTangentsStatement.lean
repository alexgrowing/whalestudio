import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsStableEigenTangents
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StableEig
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stable_eigen_tangents : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (X : Scheme.{0}) (t : SAB H X) (A : Type) [CommRing A] [IsLocalRing A] (x : Sp A ⟶ X) (κ : c.F →+* A) (σ : E →+* ℂ), ∃ (r : ℕ) (e : Fin r → (epsAt x ⟶ t.G)), StableEig t x κ σ e := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFn.EigStalk.exists_stableEig | exact GlobalTheory.CompanionTheory.Ar.LocFn.EigStalk.exists_stableEig | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFn.EigStalk.exists_stableEig <;> assumption)
