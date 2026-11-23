import Mathlib
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBareNormDisc
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormLeOneIffLogValuation
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.KappaIntegralBound
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

namespace PositivityTheory.Xgn.PlaceValuation

theorem exists_place {K : Type} [Field K] [NumberField K] (p : Nat.Primes) (κ : K →+* ℂ_[p]) :
    ∃ la : HeightOneSpectrum (𝓞 K), ∀ a : K, la.valuation K a ≤ 1 ↔ ‖κ a‖ ≤ 1 :=
  _root_.Bl.KappaIntegralBound.goal1 p κ

theorem place_unique {K : Type} [Field K] [NumberField K] {p : Nat.Primes} {κ : K →+* ℂ_[p]}
    {la la' : HeightOneSpectrum (𝓞 K)} (h : ∀ a : K, la.valuation K a ≤ 1 ↔ ‖κ a‖ ≤ 1)
    (h' : ∀ a : K, la'.valuation K a ≤ 1 ↔ ‖κ a‖ ≤ 1) : la = la' :=
  HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := K)
    (Valuation.isEquiv_iff_val_le_one.2 fun {a} => (h a).trans (h' a).symm)

theorem log_norm_ne_zero {K : Type} [Field K] [NumberField K] {p : Nat.Primes} {κ : K →+* ℂ_[p]}
    {la : HeightOneSpectrum (𝓞 K)} (h : ∀ a : K, la.valuation K a ≤ 1 ↔ ‖κ a‖ ≤ 1) {π : K}
    (hπ : la.valuation K π = WithZero.exp (-1 : ℤ)) : Real.log ‖κ π‖ ≠ 0 := by
  have h1 : ¬ la.valuation K π⁻¹ ≤ 1 := by
    rw [map_inv₀, hπ, ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  rw [h, map_inv₀, norm_inv, not_le] at h1
  have := Real.log_pos h1
  rw [Real.log_inv] at this
  linarith

end PositivityTheory.Xgn.PlaceValuation

theorem PositivityTheory.Xgn.line_function_place_valuation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (Z : Formalism.L2.Pj.Comp Xo c) (τ : GlobalTheory.AllWt.Psi H) (s : Formalism.L2.Pj.Rul Xo c) (φ : FrameFn Xo c) (ρ : HeightOneSpectrum (𝓞 c.F) → ℝ), IsLineFn (Z : Set (Xo.XF c)) τ.1 φ → Reads (Z : Set (Xo.XF c)) τ.1 s φ → (∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (la : HeightOneSpectrum (𝓞 c.F)) (π : c.F), (∀ a : c.F, la.valuation c.F a ≤ 1 ↔ ‖κ a‖ ≤ 1) → la.valuation c.F π = WithZero.exp (-1 : ℤ) → HasFinNorm (Z : Set (Xo.XF c)) τ.1 φ p κ (ρ la * Real.log ‖κ π‖)) → ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, v s = (ρ la : EReal) := by
  intro E _ _ _ H D l Xo c _ Z τ s φ ρ hφ hs hN la v hv
  choose pl hpl using fun (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) => PositivityTheory.Xgn.PlaceValuation.exists_place p κ
  choose un hun using fun la : HeightOneSpectrum (𝓞 c.F) => la.valuation_exists_uniformizer c.F
  obtain ⟨⟨_, T, io, e, ho, y, hy, eta, -, rfl⟩, rfl⟩ := hv
  letI := io.toAlgebra
  obtain ⟨p, κ, hκ, hval⟩ := GlobalTheory.CompanionTheory.Ar.Flat.nval_flat_rule E H D l Xo c (Z : Set (Xo.XF c)) τ.1 φ s
    (fun p κ => ρ (pl p κ) * Real.log ‖κ (un (pl p κ))‖) τ.2 hφ hs
    (fun p κ => hN p κ (pl p κ) _ (hpl p κ) (hun _)) la T io e y (GlobalTheory.AllWt.ptF y.1) ho hy.1
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (by rintro _ ⟨x, rfl⟩; exact hy.2 x)
  have hla : pl p κ = la := PositivityTheory.Xgn.PlaceValuation.place_unique (hpl p κ) hκ
  refine (hval (un la) (hun la)).trans ?_
  rw [hla, mul_div_assoc, div_self (PositivityTheory.Xgn.PlaceValuation.log_norm_ne_zero hκ (hun la)), _root_.mul_one]
