import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricLawsAllStates
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedThTw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DofOTw
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyPtsOfReading
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_laws_all_states : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ _ _ _ _ P x => ∀ (l : SeriesLevel hL x) (i : (Dof x).ntw.Tw), GlobalTheory.GeoTie.GeoLaws l.b.YS x.m.z.geo.fw ((Dof x).nth.iC i) := by
  first | exact @GlobalTheory.HeightCounting.Up.geometric_laws_of_lb1 | exact GlobalTheory.HeightCounting.Up.geometric_laws_of_lb1 | (intros; apply GlobalTheory.HeightCounting.Up.geometric_laws_of_lb1 <;> assumption)
