import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedNullSetCharts
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTChartSource
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O
open MeasureTheory GlobalTheory.ChartGlue GlobalTheory.Mean4O.CoverInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closed_null_set_charts : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (e : ℕ) (M : Man e) (I : ManIs M Y) (ε : (𝓞 F →+* ℂ) → Fin (M.n + 1)) (π : ∀ σ, CxPts V.p σ → M.X (ε σ)), Y.dim = e → V.IsDown I ε π → ∀ σ, ∃ T : Set (M.X (ε σ)), IsClosed T ∧ (∀ c : AlgChart Y.str (I.ε (ε σ)) e, MeasureTheory.volume ((tChart I c) '' ((tChart I c).source ∩ T)) = 0) ∧ (∀ c : AlgChart V.p σ e, MeasureTheory.volume (c.e '' (c.e.source ∩ π σ ⁻¹' T)) = 0) ∧ (∀ x ∉ T, (π σ ⁻¹' {x}).encard = V.deg) ∧ ∀ z, π σ z ∉ T → ∃ (c : AlgChart Y.str (I.ε (ε σ)) e) (c' : AlgChart V.p σ e), z ∈ c'.e.source ∧ I.pt _ (π σ z) ∈ c.e.source ∧ ∀ w ∈ c'.e.source, I.pt _ (π σ w) ∈ c.e.source → c'.e w = c.e (I.pt _ (π σ w)) := by
  first | exact @GlobalTheory.Mean4O.CoverExc.exists_exceptional | exact GlobalTheory.Mean4O.CoverExc.exists_exceptional | (intros; apply GlobalTheory.Mean4O.CoverExc.exists_exceptional <;> assumption)
