import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootOriginHeightComparisonThree
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLatFlagPair
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SplitComps
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArMonoReline
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm blockFnField)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_height_comparison_three : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S₀ S : Finset ℕ) (M₀ M₁ Rf : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (o₀ : RootOrigin Y S₀ M₀ Fx) (o₁ : RootOrigin Y S M₁ Fx) (oR : RootOrigin Y ∅ Rf Fx) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (κ₀ : M₀.K → K) (v₀ : (Σ k, M₀.ι k) → Σ k, J k) (κ₁ : M₁.K → K) (v₁ : (Σ k, M₁.ι k) → Σ k, J k) (κR : Rf.K → K) (vR : (Σ k, Rf.ι k) → Σ k, J k) (i₀ : M₀.Ω →+* Ω) (i₁ : M₁.Ω →+* Ω) (iR : Rf.Ω →+* Ω), IsBlockMap κ₀ v₀ → IsBlockMap κ₁ v₁ → IsBlockMap κR vR → (∀ p, y (v₀ p) = i₀ (M₀.y p)) → (∀ p, y (v₁ p) = i₁ (M₁.y p)) → (∀ p, y (vR p) = iR (Rf.y p)) → i₀.comp o₀.g = iR.comp oR.g → i₁.comp o₁.g = iR.comp oR.g → o₀.Re.J = ⊤ → o₁.Re.J = ⊤ → oR.Re.J = ⊤ → oR.Fl.deg = 1 → IsArithVar (mCoordIdeal y) (dimFl (CMType H) (D.p + D.q) + 1) → ∀ (r : CMType H × Fin (D.p + D.q)) (f g : MvPolynomial (Σ k, J k) ℤ) (bf bg : K → ℕ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f bf → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog g bg → (fun k => (bf k : ℤ) - bg k) = pullDeg κ₀ (M₀.xdeg r) - pullDeg κ₁ (M₁.xdeg r) → f ∉ mCoordIdeal y → g ∉ mCoordIdeal y → aeval y f = i₁ (o₁.e r) / i₀ (o₀.e r) * aeval y g → ∀ t, 0 < t → t ≤ Sys.t₀ → ∀ z ∈ mcPts (mCoordIdeal y), ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) f)‖ * (M₁.x t r).h (fun p => z (v₁ p)) = ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) g)‖ * (M₀.x t r).h (fun p => z (v₀ p)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.OrIso.root_isometric | exact GlobalTheory.CompanionTheory.Ar.OrIso.root_isometric | (intros; apply GlobalTheory.CompanionTheory.Ar.OrIso.root_isometric <;> assumption)
