import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPendingObjectsDepthZeroAdmissibleEigenSpanStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraCentreKeepsTypeSpacesAtLocalisationsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroOfLabelsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmDZOfLabelsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameGenAtTransport
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.PinClose

theorem main : GlobalTheory.NRows.Hypotheses₂ → GlobalTheory.Published.DepthZeroInertia → GlobalTheory.Published.DepthZeroWild → GlobalTheory.Published.DepthZeroSupport →
    ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) →
    LabAll D P.T → GlobalTheory.HeightCounting.Up.CenLoc D P.M → GreenLab P.ty.grp → ChiTOk D P.cf → SumRepresentations.tie0 D → SumRepresentations.adm5 D →
    ZLStable D → CenInt D → SerLL D → CoeffRingsHaveRootsOfUnity D → ∃ Q : PairedCharacterCondition.Pend D, PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q := by
  intro hPr hIn hWi hSu hL D P hRow hLab hCen hGr hChi ht0 ha5 hZL hCI hSer hZ
  obtain ⟨hIne, hDep, hGen⟩ := GlobalTheory.LabTies.main D P.T hLab
  have hCT : OnMtPreservesTypeV D := GlobalTheory.T.groupAlgebraCentre_keeps_typeSpaces_at_localisations D P.M P.H.av hCen
  have hDZ : DepthZ D := GlobalTheory.T.depth_zero_of_labels hPr hWi hSu hL D P hRow hLab hChi
  have hAdm : PairedCharacterCondition.RT.AdmDepthZeroTypes (D := D) := GlobalTheory.T.admDZ_of_labels hPr hIn hL D P hRow hLab hCen hGr hChi
  have hPar : ∀ S : Formalism.L2.ParC D, ∃ σ' : D.ntypes.Par,
      ∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut S.1 w := by
    intro S
    refine ⟨P.ty.par.eP.symm ⟨S.1, S.2⟩, fun w => ?_⟩
    rw [P.ty.par.locPar_def]
    have e := P.ty.par.eP.apply_symm_apply (⟨S.1, S.2⟩ : HeightCounting.ParC D)
    rw [e]
  exact GlobalTheory.T.exists_pending_objects_depthZero_admissible_eigenSpan D P.M P.H.hecke P.H.rational P.H.av hPar ht0 ha5 hIne hDep hGen hZL hCI hCT hSer hZ hDZ hAdm

end GlobalTheory.PinClose
