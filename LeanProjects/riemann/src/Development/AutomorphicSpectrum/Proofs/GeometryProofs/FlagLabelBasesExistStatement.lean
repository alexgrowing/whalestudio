import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagLabelBasesExist
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
theorem _root_.GlobalTheory.T.flag_label_bases_exist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag), ∃ m : ℕ, 0 < m ∧ ∀ (s : CMType H ⊕ CMType H) (p : Cpt 𝔐.ξ), ∃ (b : Fin (labelRk D s) → 𝔐.Li) (π : Fin (labelRk D s) → Module.Dual Ω 𝔐.Li), (∀ i, flagStep Ω b i = flagStep Ω (Fl.b s) i) ∧ (𝔐.V s).IsFrameAt b p ∧ (∀ i, (m : Ω) • b i ∈ 𝔐.M.lat p) ∧ (∀ i j, π i (b j) = if i = j then 1 else 0) ∧ ∀ i, ∀ e ∈ 𝔐.M.lat p, (m : Ω) * π i e ∈ regAt 𝔐.ξ p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sandwich.lat_sandwich | exact GlobalTheory.CompanionTheory.Ar.Sandwich.lat_sandwich | (intros; apply GlobalTheory.CompanionTheory.Ar.Sandwich.lat_sandwich <;> assumption)
