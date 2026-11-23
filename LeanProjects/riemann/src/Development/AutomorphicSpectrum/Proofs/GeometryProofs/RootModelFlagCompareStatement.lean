import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootModelFlagCompare
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_model_flag_compare : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) [Fintype (CMType H)] (M R : Top.RootModel (CMType H) (D.p + D.q)) (𝔐 : HodgeCpt Y S M.y) (𝔐₀ : HodgeCpt Y S₀ R.y) (Fl : 𝔐.Flag) (Fl₀ : 𝔐₀.Flag) (i : R.Ω →+* M.Ω) (e : CMType H × Fin (D.p + D.q) → M.Ω) (e₀ : CMType H × Fin (D.p + D.q) → R.Ω), 𝔐.ξ ≫ 𝔐.f = spMap i ≫ 𝔐₀.ξ ≫ 𝔐₀.f → (∀ s k, (𝔐.M.pt (Fl.b s k)).left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (𝔐₀.M.pt (Fl₀.b s k)).left ≫ 𝔐₀.m.φ) → Fl.RootLines M.xdeg e → Fl₀.RootLines R.xdeg e₀ → ∀ r, Ht.GenUnit (Ht.joinOf M R i) (Ht.joinDeg M R (some r)) (i (e₀ r) / e r) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.CloseGen.genUnit_join | exact GlobalTheory.CompanionTheory.Ar.Ht.CloseGen.genUnit_join | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.CloseGen.genUnit_join <;> assumption)
