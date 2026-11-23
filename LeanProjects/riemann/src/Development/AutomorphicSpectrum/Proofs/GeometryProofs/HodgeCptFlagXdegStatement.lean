import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFlagXdeg
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_cpt_flag_xdeg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω), Function.Injective β → Fl.RootLines xdeg e → ∀ r, ∃ A : HermLine J, A.a = xdeg r ∧ Fl.IsHodgeLine r (e r) A ∧ IsConjInvariantH A := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeLine.exists_hodgeLine | exact GlobalTheory.CompanionTheory.Ar.HodgeLine.exists_hodgeLine | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeLine.exists_hodgeLine <;> assumption)
