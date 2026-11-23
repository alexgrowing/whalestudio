import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowLatticeSelfDualComponentsRescaledWordFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowLattice_selfDual_components_rescaled_word_frame : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (μ lam : D.host.E), GlobalTheory.Core.Mi.IdE X → B.FrameAt μ lam → IsSelfDualC (D.sp.Y 0) (latS D) ∧ (∀ y ∈ latS D, ∀ i, (fun r => (B.d.qX *ᵥ y) i * B.d.e r i) ∈ latS D ∧ (fun r => (B.d.qY *ᵥ y) i * B.d.e' r i) ∈ latS D) ∧ (∀ (i : Fin D.R.rS) (t : D.host.E), t • (fun r => B.d.e r i) ∈ latS D ↔ GlobalTheory.Core.SBesEx.scl μ lam i * t ∈ aaD D i) ∧ ∀ (i : Fin D.R.rS) (t : D.host.E), t • (fun r => B.d.e' r i) ∈ latS D ↔ (star (GlobalTheory.Core.SBesEx.scl μ lam i))⁻¹ * t ∈ (aaD D i)⁻¹ := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.latS_rescaled_frame | exact GlobalTheory.Core.Mi.LatMatch.latS_rescaled_frame | (intros; apply GlobalTheory.Core.Mi.LatMatch.latS_rescaled_frame <;> assumption)
