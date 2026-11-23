import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedChartHolomorphicCompat
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTChartSource
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O
open MeasureTheory GlobalTheory.ChartGlue GlobalTheory.Mean4O.CoverInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transported_chart_holomorphic_compat : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (e : ℕ) (M : Man e) (I : ManIs M Y) (a : Fin (M.n + 1)) (P : LocPot (M.X a)), IsPotential (M.A a) P → (∀ c c' : AlgChart Y.str (I.ε a) e, DifferentiableOn ℂ (tChart I c' ∘ (tChart I c).symm) (ReciprocityTheory.L2DbarEstimates.Y.ovl (fun c : AlgChart Y.str (I.ε a) e => tChart I c) c c')) ∧ ∀ (c c' : AlgChart Y.str (I.ε a) e) (x : M.X a), x ∈ (tChart I c).source → x ∈ (tChart I c').source → potDens I P c x = ‖GlobalTheory.ChartGlue.transDet (tChart I c) (tChart I c') x‖ ^ 2 * potDens I P c' x := by
  first | exact @GlobalTheory.Mean4O.CoverInt.potDens_chartRule | exact GlobalTheory.Mean4O.CoverInt.potDens_chartRule | (intros; apply GlobalTheory.Mean4O.CoverInt.potDens_chartRule <;> assumption)
