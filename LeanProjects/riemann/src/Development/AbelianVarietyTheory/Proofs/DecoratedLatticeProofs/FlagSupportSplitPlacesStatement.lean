import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagSupportSplitPlaces
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BesselCompatibility
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_support_split_places : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A), GlobalTheory.Core.Mi.IdE X → ∀ (PP : Formalism.L2.DIV.Pl D.host.E) (e : AE D), IsSplitIdem D e → Formalism.L2.NTheta.IsIdemAt e PP → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → ∀ n ∈ flagN B.d, Formalism.L2.Theta.SuppAt e (D.sp.Y 0) n → ((iotaX X h).symm (1, X.xu u))⁻¹ * n * ((iotaX X h).symm (1, X.xu u)) ∈ rowJ X h → rowChi X h (((iotaX X h).symm (1, X.xu u))⁻¹ * n * ((iotaX X h).symm (1, X.xu u))) = psiBes ψ B.d 1 (vecB B.o B.ζ) n := by
  first | exact @GlobalTheory.RowBesChar.rowChi_conj_eq_psiBes | exact GlobalTheory.RowBesChar.rowChi_conj_eq_psiBes | (intros; apply GlobalTheory.RowBesChar.rowChi_conj_eq_psiBes <;> assumption)
