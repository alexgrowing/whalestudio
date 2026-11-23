import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptIsVectorBundleRank
import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeCpt_isVectorBundle_rank : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀), ∀ s, (LL 𝔐 s).IsVB (rk (CMType H) D.p D.q s) (VV 𝔐 s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.LL_isVB | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.LL_isVB | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.LL_isVB <;> assumption)
