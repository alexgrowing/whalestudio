import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeightSectionComponentValue
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntMemModelSmall
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProdZpowLe
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_section_component_value : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw) (f : Rul Xo c), f ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw u 0) → ∀ (B' : Finset (Om Z)) (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ → ∀ y : IntFr Xo c T io, y.IsAlg → (letI := io.toAlgebra; GlobalTheory.AllWt.LiesOn Z y.1) → evI y f ≠ 0 → ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (e' : ℕ) (y' : IntFr Xo c T' io') (A : Subring (Om Z)) (ev : A →+* T'.Fr), OverLa la T'.V io' e' ∧ y'.IsAlg ∧ nval T'.V e' (evI y' f) = nval T.V e₀ (evI y f) ∧ (↑B' : Set (Om Z)) ⊆ A ∧ (∀ b ∈ B', b ≠ 0 → b⁻¹ ∈ A) ∧ (∀ x, IsAlgebraic ℤ (ev x)) ∧ FinTr.RegAt h Z io' A ev y'.1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.FinTr.Approx.approx_main | exact GlobalTheory.CompanionTheory.Ar.Plug.FinTr.Approx.approx_main | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.FinTr.Approx.approx_main <;> assumption)
