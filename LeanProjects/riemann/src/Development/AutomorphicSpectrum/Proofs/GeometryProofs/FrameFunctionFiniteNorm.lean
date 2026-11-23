import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBareNormDisc
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FinConstFor
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatZeroFromResolutionAndGagaStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteConstantAllHoldsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodReductionDvrModelExistsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IrreducibleComponentClopenStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionTwoModelsRelayStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Br.FinGood

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

theorem finGood : Geo.ResK.ResKStatement → GagaSections → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (φ : FrameFn Xo c) (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), FracBase β → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → U ∈ irreducibleComponents (Xo.XF c) → Z.IsGeom → FlatOnModel Z τ φ → l.GoodAt p → ∃ t : ℝ, HasFinNorm U τ φ p κ t := by
  intro hRes hGaga E _ _ _ H D l Xo c O _ β Y U Z τ φ p κ hβ hpq hrt hU hZ hφ hgood
  obtain ⟨O', _, _, _, β', Y', hβ', hκ, hsplit, hN3⟩ := GlobalTheory.T.good_reduction_dvr_model_exists E H D l Xo c p κ hpq hgood
  obtain ⟨-, hne, hgeom⟩ := GlobalTheory.T.irreducible_component_clopen E H D l Xo c U hU
  obtain ⟨Z'⟩ := hne O' β' Y' hβ'
  have hZ' : Z'.IsGeom := hgeom O β Y O' β' Y' Z Z' hβ hβ' hZ
  obtain ⟨φ', hline', hflat', -⟩ := GlobalTheory.T.flat_zero_from_resolution_and_gaga hRes hGaga E H D l Xo c O' β' Y' U Z' τ hβ' hpq hrt hZ'
  obtain ⟨t', ht'⟩ := GlobalTheory.T.finite_constant_all_holds E H D l Xo c O' β' Y' U Z' τ p κ φ' hrt hβ'.1 hκ hsplit hN3 hZ' hflat' hline'
  obtain ⟨x, hx0, hx⟩ := GlobalTheory.T.frame_function_two_models_relay hRes hGaga E H D l Xo c O β Y O' β' Y' U Z Z' τ φ φ' hβ hβ' hpq hrt hZ hZ' hφ hflat'
  refine ⟨t' - Real.log ‖κ x‖, ?_⟩
  unfold GlobalTheory.CompanionTheory.Ar.Fl.HasFinNorm
  intro V K _ _ _ _ _ _ j β₁ y v w T tK m m' hj hjβ hfr hv hw
  have h1 := ht' V K j β₁ y v w T tK m m' hj hjβ hfr hv hw
  have hjx : j (β₁ x) = κ x := by rw [← hjβ]; rfl
  have hφne : j (φ K y v w) ≠ 0 := (map_ne_zero j).mpr (hφ.1.ne K β₁ y v w hfr)
  have hxne : j (β₁ x) ≠ 0 := (map_ne_zero j).mpr ((map_ne_zero β₁).mpr hx0)
  rw [hx K β₁ y v w hfr, map_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hxne) (norm_ne_zero_iff.mpr hφne), hjx] at h1
  linarith

end GlobalTheory.CompanionTheory.Ar.Br.FinGood
