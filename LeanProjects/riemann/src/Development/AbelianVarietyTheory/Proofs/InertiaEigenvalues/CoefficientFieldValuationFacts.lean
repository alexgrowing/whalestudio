import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AuxiliaryPrimeNeTypePrime
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsEmptyOfNotAll
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallySizesCongruencesHostFactsColumnChoicesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AtMemAnd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyDefiniteSpacesStandardAndLarge
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.GalLoc.FieldAt

theorem field_at : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t nch n c =>
    ValLL0 (w.D Z) (TC.cf w.I w.l Z) ∧ (∀ (k : Fin 2) (z : ℂ), z ^ ((w.D Z).host.g k * ((w.D Z).host.g k - 1)) = 1 → z ∈ (embLL0 (w.D Z)).fieldRange) ∧ (∀ x : (w.D Z).LL0, star (x : (w.D Z).what₂.LL) ∈ (w.D Z).LL0) := by
  intro hP _ hL
  have h1 := GlobalTheory.TwInputs.SmallField.evLgG_fieldOk hP
  have h2 := (evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev).inter (evG_of_ev GlobalTheory.Mem.StdSize.vstd_size_ev)
  refine (h1.inter h2).imp fun K _ _ _ _ hK => ?_
  obtain ⟨hF, hH, hV⟩ := hK
  refine hF.imp fun B f T hO hF' => ?_
  intro hKP w Z Wt p0 t nch n xd c _ _ _
  obtain ⟨hX, -⟩ := hF' hKP T w Z
  have hHH := (hH (w.st Z) hO).1
  obtain ⟨hVs, hs⟩ := hV (w.st Z) hO
  have F := hX (GlobalTheory.TwInputs.JoinModel.realOf t hHH hVs hs) t.r.z.lev.C
  refine ⟨?_, F.roots, F.star⟩
  have v : ValLL0 (w.D Z) t.r.z.R.C := F.vals
  have e : t.r.z.R.C = TC.cf w.I w.l Z := t.r.z.lev.C
  rw [← e]
  exact v

end GlobalTheory.GalLoc.FieldAt
