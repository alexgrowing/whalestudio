import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootMetricFinitelyManyPlaces
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_metric_finitely_many_places : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (P : Finset ℕ) (x : DV.Rt D.what₂.Tau O.N) (y : AlgPt (O.var c)), (∀ st : ((D.host.E →+* ℂ) × ℕ) ⊕ ℕ, (letterOf O.S.Dw st).isSome → {v : HeightOneSpectrum (𝓞 D.what₂.LL) | ∃ e : TrueGeo.Ext v, (O.adl0 c (Finsupp.single (ArIn.ind P, none, st) 1)).lg v e y ≠ 0}.Finite) → {v : HeightOneSpectrum (𝓞 D.what₂.LL) | ∃ e : TrueGeo.Ext v, (O.root0 c P x).lg v e y ≠ 0}.Finite := by
  first | exact @GlobalTheory.Mean4O.Setup.finite_root0_lg | exact GlobalTheory.Mean4O.Setup.finite_root0_lg | (intros; apply GlobalTheory.Mean4O.Setup.finite_root0_lg <;> assumption)
