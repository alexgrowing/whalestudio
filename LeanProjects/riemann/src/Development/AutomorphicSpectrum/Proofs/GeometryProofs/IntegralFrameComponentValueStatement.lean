import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralFrameComponentValue
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
theorem _root_.GlobalTheory.T.integral_frame_component_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (Z : Comp Xo c) (ex : Ix Dw → ℤ) (f : Rul Xo c), f ∈ GlobalTheory.AllWt.secZ Xo c ex → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (A : Subring (Om Z)) (ev : A →+* T.Fr), FinTr.RegAt h Z io A ev y.1 → evI y f ≠ 0 → ∀ hb : evC h Z f ∈ A, ev ⟨_, hb⟩ ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.FinTr.ev_genValue_ne_zero | exact GlobalTheory.CompanionTheory.Ar.Plug.FinTr.ev_genValue_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.FinTr.ev_genValue_ne_zero <;> assumption)
