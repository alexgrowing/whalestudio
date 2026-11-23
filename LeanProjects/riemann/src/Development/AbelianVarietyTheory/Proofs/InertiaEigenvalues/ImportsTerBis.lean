import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTrueReadingWithLawsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameCharacterLabelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlaceOfOverTypePrimeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChiDeRhamWeilDeligneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabRcAtMulUnr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameLabelDeterminantStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TieChiPin

theorem main : GlobalTheory.NRows.Hypotheses₂ → GlobalTheory.Published.DepthZeroInertia → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → LabAll D P.T → ChiTOk D P.cf → PairedCharacterCondition.tieChi (D := D) := by
  intro hPr hDZ hL D P hRow hLab hChi i k hl v
  obtain ⟨S, hS, -, -⟩ := GlobalTheory.T.exists_true_reading_with_laws hPr.fin hL D P hRow
  have hsp : IsSplitPl D.host (D.naut.plGw k v) := GlobalTheory.T.isSplitPlace_of_over_type_prime D k _ (D.naut.plGw_over k v)
  obtain ⟨htame, hχ, u, hu, hlab⟩ := GlobalTheory.T.tame_character_label hPr hDZ hL D P hChi S hS i k v hsp
  refine ⟨u, hu, fun w hw => ⟨fun hw0 => ?_, fun hc => ?_⟩⟩
  · obtain ⟨hdR, hwd⟩ := GlobalTheory.T.chi_de_rham_weil_deligne hPr hL D P i w hw
    refine ⟨hdR, ?_⟩
    rw [hwd, hw0]
    rw [GlobalTheory.LabFixed.labFixed hPr hL D P S hS i k v hsp hχ, hlab]
  · obtain ⟨hdR, hwd⟩ := GlobalTheory.T.chi_de_rham_weil_deligne hPr hL D P i w hw
    refine ⟨hdR, ?_⟩
    rw [hwd]
    exact GlobalTheory.T.tame_label_determinant hPr hL D P hLab S hS i k v hsp hχ u htame hlab w hc _

end GlobalTheory.TieChiPin
