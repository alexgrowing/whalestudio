import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMetricFinitelyManyPlaces
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_metric_finitely_many_places : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (V : Cover Y) (A : Adl C Y) (L : HermLB V.p) (k : ℕ), k ≠ 0 → V.Induces A L k → ∀ y : AlgPt Y, {v : HeightOneSpectrum (𝓞 F) | ∃ e : TrueGeo.Ext v, A.lg v e y ≠ 0}.Finite := by
  first | exact @GlobalTheory.Mean4O.Cover.finite_places_lg_ne_zero | exact GlobalTheory.Mean4O.Cover.finite_places_lg_ne_zero | (intros; apply GlobalTheory.Mean4O.Cover.finite_places_lg_ne_zero <;> assumption)
