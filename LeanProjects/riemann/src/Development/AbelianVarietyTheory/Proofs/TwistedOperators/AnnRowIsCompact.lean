import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFiniteAdelicMatrixLatticeDepthLatticeOfPair
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IsSelfDualCOfBase
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousSmulMx
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.RowAnn

theorem annRow_isCompact : All fun {D} _ _ {sc} {G} W _ => ∀ i, i < D.R.m → IsCompact {u' : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) | MxAt (fun _ => True) u' ∧ ∀ u ∈ latRow G i, W.ψ (symplO _ _ u u') = 1} := by
  intro D _ T L μ0 hL sc G W M _ i hi

  have hsd : ∀ k, k ≤ D.R.m → IsSelfDualC (G.V (.grid k 0)) (G.Λ (.grid k 0)) := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    ·
      obtain ⟨c, hc⟩ := hL.βY 0 (Nat.lt_of_le_of_lt (Nat.zero_le i) hi)
      have hY := Formalism.IndefR.Eqv.KerDiag.isSelfDualC_of_base hc
      show IsSelfDualC (G.node (.grid 0 0)).sp (G.node (.grid 0 0)).lat
      rw [G.node_zero_zero]
      exact hY
    ·
      refine (G.isV (X := .grid k 0) ⟨hk, Nat.zero_le _⟩ ?_).sd
      intro j hj
      injection hj with h1 h2
      omega

  have hfin : FinLat (latRow G i) :=
    GlobalTheory.AscFin.DepLat.finLat_depLat G (.chi i 0) (isSelfDualC_neg (hsd (i + 1) hi)) (hsd i hi.le)
  obtain ⟨U, hU, h0, hUΓ⟩ := hfin.opn
  exact GlobalTheory.AnnNbhdCpt.isCompact_annSet W.ψ W.ψ_std _ _ (latRow G i) U hU h0 hUΓ

end GlobalTheory.AscFin.RowAnn

end
