import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsXdAllIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOneOfIsOfFinOrderOfCharpoly
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisSideStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistOfPlaceInWeightSetStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AllTriplesLocalStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.HeightCounting.Up.TripFin

theorem triplesGood : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL,
    AtMem hL fun _ _ _ _ w Z _ _ t nch n c => GlobalTheory.PtCore.TriplesGood (w.D Z) := by
  intro hP hS hL
  have h := Model.AtMem.and (Model.AtMem.and (GlobalTheory.T.exists_galois_side hP hS hL) (GlobalTheory.T.twist_of_place_in_weight_set hP hS hL)) (GlobalTheory.T.all_triples_local hP hS hL)
  refine Model.AtMem.imp h ?_
  rintro K B f T w Z Wt p0 t nch n c ⟨⟨⟨G, -, -, -⟩, hW⟩, hA⟩ a σ Sg h1 h2
  obtain ⟨s, hs⟩ := hA a σ Sg h1 h2
  exact ⟨s, hs, (GlobalTheory.Triple.satake_identity_of_isTriple _ G.triple).2.1 _ (hW a) s⟩

end GlobalTheory.HeightCounting.Up.TripFin
