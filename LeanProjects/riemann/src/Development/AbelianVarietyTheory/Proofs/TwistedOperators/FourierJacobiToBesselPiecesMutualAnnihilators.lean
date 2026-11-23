import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplOZeroRight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiDepthLatticeKeepsIsotropicHomPartStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AnnRowIsCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatRowAnnOpen
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeFirstRowEqDoubleAnnihilatorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.AnnPieces

theorem pcFB_dualA : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), FinLat (pcFB W F σ h h').A₂ ∧ (∀ a, MxAt (fun _ => True) a → (a ∈ (pcFB W F σ h h').A₁ ↔ ∀ a' ∈ (pcFB W F σ h h').A₂, W.ψ (symplO _ _ ((F.dJ (σ + 1) h).extX _ a) ((F.dJ (σ + 1) h).extY _ a')) = 1)) ∧ (∀ a', MxAt (fun _ => True) a' → (a' ∈ (pcFB W F σ h h').A₂ ↔ ∀ a ∈ (pcFB W F σ h h').A₁, W.ψ (symplO _ _ ((F.dJ (σ + 1) h).extX _ a) ((F.dJ (σ + 1) h).extY _ a')) = 1)) := by
  intro D hD T L μ0 hL sc G W M hM F hF σ h h'
  have hi : 2 * σ + 2 < D.R.m := by omega
  refine pieces_dualA (d := F.dJ (σ + 1) h) (ψ := W.ψ) (Γ := latRow G (2 * σ + 2)) (F.dB σ h') (latBig G (2 * σ + 2))
    (GlobalTheory.T.jacobi_depth_lattice_keeps_isotropic_hom_part D hD T L μ0 hL sc G W M hM F hF σ h) (GlobalTheory.AscFin.RowAnn.annRow_isCompact D hD T L μ0 hL sc G W M hM _ hi) (GlobalTheory.AscFin.AnnOpen.latRow_ann_open D hD T L μ0 hL sc G W M hM _ hi) ?_
  intro u hu hb
  exact GlobalTheory.T.depthLatticeFirstRow_eq_doubleAnnihilator D hD T L μ0 hL sc G W M hM _ hi u hu fun u' hu' hv => hb u' ⟨hu', hv⟩

end GlobalTheory.AscFin.AnnPieces

end
