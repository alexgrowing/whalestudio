import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HessianRelationChartCompat
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTChartSource
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O
open MeasureTheory GlobalTheory.ChartGlue GlobalTheory.Mean4O.CoverInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hessian_relation_chart_compat : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (e : ℕ) (M : Man e) (I : ManIs M Y) (ε : (𝓞 F →+* ℂ) → Fin (M.n + 1)) (π : ∀ σ, CxPts V.p σ → M.X (ε σ)) (L : HermLB V.p) (P : M.Pot), HessRel ε π L P → ∀ σ, Continuous (π σ) → ∀ (c : AlgChart Y.str (I.ε (ε σ)) e) (c' : AlgChart V.p σ e), (∀ w ∈ c'.e.source, I.pt _ (π σ w) ∈ c.e.source → c'.e w = c.e (I.pt _ (π σ w))) → ∀ w ∈ c'.e.source, I.pt _ (π σ w) ∈ c.e.source → c'.chernDens (L.φ σ) w = potDens I (P (ε σ)) c (π σ w) := by
  first | exact @GlobalTheory.Mean4O.CoverInt.chernDens_eq_potDens | exact GlobalTheory.Mean4O.CoverInt.chernDens_eq_potDens | (intros; apply GlobalTheory.Mean4O.CoverInt.chernDens_eq_potDens <;> assumption)
