import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SupportedStabilizerConjSatisfiesDeepCongruence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supportedStabilizer_conj_satisfies_deepCongruence : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (v : GlobalTheory.FinPl.Pl D), ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal → ∀ κ : GA D (D.sp.Y 0), κ ∈ grpAt (D.sp.Y 0) (· = v) → (iotaX X h κ).2 ∈ X.B.I.Kset → K2cong X.B.I X.B.g X.e0 X.z0 X.bw ((X.xu u)⁻¹ * (iotaX X h κ).2 * X.xu u) := by
  first | exact @GlobalTheory.Core.Mi.KTwoAwayLevel.k2cong_conj_of_grpAt | exact GlobalTheory.Core.Mi.KTwoAwayLevel.k2cong_conj_of_grpAt | (intros; apply GlobalTheory.Core.Mi.KTwoAwayLevel.k2cong_conj_of_grpAt <;> assumption)
