import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSelfDualLatticeIffIntegralFrameMatricesHalf
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelOneClassEqClassicalShortSeries
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_selfDualLattice_iff_integral_frameMatrices_half : ∀ {D : D7} {S T : HSp D} {F : GlobalTheory.ExportSeries.Frame S T}, F.Good → ∀ {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)},
    GlobalTheory.ExportSeries.PlacesOK Pg Q → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ {x : WO S T}, IsHalf (GlobalTheory.ExportSeries.halfIdem Pg Q) x →
      (x ∈ F.lat ↔ IsIntM (frMapAdj S T F.βS F.βT x) ∧ IsIntM (frMapO S T F.βS F.βT x)) := by
  first | exact @GlobalTheory.ExportSeries.LatHalf.mem_lat_iff_isIntM_halfIdem | exact GlobalTheory.ExportSeries.LatHalf.mem_lat_iff_isIntM_halfIdem | (intros; apply GlobalTheory.ExportSeries.LatHalf.mem_lat_iff_isIntM_halfIdem <;> assumption)
