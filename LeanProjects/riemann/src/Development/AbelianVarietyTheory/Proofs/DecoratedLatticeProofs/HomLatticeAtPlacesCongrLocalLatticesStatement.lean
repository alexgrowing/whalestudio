import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeAtPlacesCongrLocalLattices
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorOneApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homLatticeAtPlaces_congr_localLattices : ∀ (D : D7) (S T : HSp D) (N M : Lat S) (N' M' : Lat T), IsSelfDualC S N → IsSelfDualC S M → IsSelfDualC T N' → IsSelfDualC T M' → ∀ (P : Pl D → Prop), (∀ p, P p → latV S N (· = p) = latV S M (· = p) ∧ latV T N' (· = p) = latV T M' (· = p)) → latO S T (N : Set _) (N' : Set _) P = latO S T (M : Set _) (M' : Set _) P := by
  first | exact @GlobalTheory.FinPl.LatCong.latO_congr | exact GlobalTheory.FinPl.LatCong.latO_congr | (intros; apply GlobalTheory.FinPl.LatCong.latO_congr <;> assumption)
