import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatHalfTensorSplitPlaceSelfDual
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorOneApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhatHalf_tensor_split_place_selfDual : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (M : Lat S) (M' : Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (P : LocPl ψ S T M M') (e : AE D), e * P.q.e = 0 → ∀ Φ : WO S T → ℂ, IsSBHalf e (latO S T (M : Set _) (M' : Set _) fun _ => True) Φ → ∀ Ψ ∈ SB (Matrix P.Y P.Y' P.k), IsSBHalf (e + P.q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) ((ofSplit P.q).tensorAt P.FS P.FT Φ Ψ) := by
  first | exact @GlobalTheory.TensorLatO.isSBHalf_tensorAt_latO | exact GlobalTheory.TensorLatO.isSBHalf_tensorAt_latO | (intros; apply GlobalTheory.TensorLatO.isSBHalf_tensorAt_latO <;> assumption)
