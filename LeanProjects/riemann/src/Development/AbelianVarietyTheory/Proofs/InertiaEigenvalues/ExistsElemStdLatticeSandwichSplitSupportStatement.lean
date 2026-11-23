import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsElemStdLatticeSandwichSplitSupport
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_elem_stdLattice_sandwich_splitSupport : ∀ (D : D7) (V : HSp D), V.gram = 1 → Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∀ (h : GA D V) (e : AE D) (Ps : Finset (Formalism.L2.DIV.Pl D.host.E)) (bad : ℕ), IsIdemSum e Ps → (∀ PP ∈ Ps, ((bad : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → SuppAt e V h → ∃ m : 𝓞 D.host.E, m ≠ 0 ∧ Ideal.span {m} • Bridge.hLat V (finPt V h) ≤ Formalism.L2.Pj.stdLat D.host.E V.rank ∧ Ideal.span {m} • Formalism.L2.Pj.stdLat D.host.E V.rank ≤ Bridge.hLat V (finPt V h) ∧ ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → m ∈ P → P.map (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) ≠ P ∧ ((bad : ℕ) : 𝓞 D.host.E) ∉ P := by
  first | exact @GlobalTheory.SuppLatStd.lat_std_of_suppAt | exact GlobalTheory.SuppLatStd.lat_std_of_suppAt | (intros; apply GlobalTheory.SuppLatStd.lat_std_of_suppAt <;> assumption)
