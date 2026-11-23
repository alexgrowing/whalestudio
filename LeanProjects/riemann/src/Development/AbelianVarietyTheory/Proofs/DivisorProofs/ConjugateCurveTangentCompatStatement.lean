import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateCurveTangentCompat
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnimodularSolCoords
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_torsion_point_compat : ∀ (K : Type) [Field K] [NumberField K] (io : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), TorsTransport io g t Λ₀ Λ₁ Ω₀ Ω₁ → ∀ (h : (curve Λ₀ Ω₀).map (g : ℂ →+* ℂ) = curve Λ₁ Ω₁) (a a' : K), (∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((t : Af K) * algebraMap K (Af K) a' - algebraMap K (Af K) a) v) ≤ 1) → pt Λ₁ Ω₁ (io a') ≫ mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) h = spMap (g : ℂ →+* ℂ) ≫ pt Λ₀ Ω₀ (io a) := by
  first | exact @GlobalTheory.CMTorsion.ConjPt.conj_pt | exact GlobalTheory.CMTorsion.ConjPt.conj_pt | (intros; apply GlobalTheory.CMTorsion.ConjPt.conj_pt <;> assumption)
