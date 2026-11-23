import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorFlag
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_cpt_interior_flag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag), Function.Injective β → ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), 𝔐.Interior z → ∀ s (i : Fin (labelRk D s)) (t : Ω), ((𝔐.V s).gr (Fl.b s) i).IsGenAt ⟨centre z, 𝔐.all _⟩ t → ∃ ν : ℝ, 0 < ν ∧ ∀ (t' : Ω) (ν' : ℝ), 𝔐.M.IsGrNorm 𝔐.t.PP.L (𝔐.V s) (Fl.b s) i z t' ν' ↔ ∃ u : ℂ, u ≠ 0 ∧ ValAt 𝔐.ξ z (t' / t) u ∧ ν' = ‖u‖ * ν := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GrNorm.exists_norm | exact GlobalTheory.CompanionTheory.Ar.GrNorm.exists_norm | (intros; apply GlobalTheory.CompanionTheory.Ar.GrNorm.exists_norm <;> assumption)
