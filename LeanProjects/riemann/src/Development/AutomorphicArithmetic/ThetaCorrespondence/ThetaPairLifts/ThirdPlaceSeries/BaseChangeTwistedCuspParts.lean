import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BaseChangeTwistedCuspPartsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StrCalcO
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSplit_of_isBCV_twistIso_of_isCuspIso : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (x : D.nd.X i) (Q P0 : D.naut.AV i) (Sig : List (Part D.naut.CG)), D.naut.ptV i Q = some x → D.naut.ptV i P0 = some x → IsCuspIso D.nd D.naut Sig → IsBCV D.nd D.naut i P0 (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) → ∀ w : HeightOneSpectrum (𝓞 D.host.E), Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → w ∉ D.nd.S i → w ∉ D.nd.Q i → D.naut.unr (D.naut.locV i Q w) → ∀ z : ℂ, D.naut.frobEig (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) = {z⁻¹} → ∃ B' : Multiset ℂ, (D.naut.frobEig (D.naut.locV i Q w)).map (fun a : ℂ => a⁻¹) = B' + GlobalTheory.DownLift.str (Ideal.absNorm w.asIdeal) z D.R.t ∧ ∀ a ∈ B', ‖a‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2) := by
  first | exact @_root_.GlobalTheory.EigStrCalc.is_split_of_cusp_iso_bcv | exact _root_.GlobalTheory.EigStrCalc.is_split_of_cusp_iso_bcv | (intros; apply _root_.GlobalTheory.EigStrCalc.is_split_of_cusp_iso_bcv <;> assumption)
end
