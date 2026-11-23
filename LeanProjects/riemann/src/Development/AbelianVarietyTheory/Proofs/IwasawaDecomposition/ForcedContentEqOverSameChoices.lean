import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowsAre
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.Top.Bl.RowWt

theorem fockDeg_cast (D : D7) (h : DV.KapDef D) (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ D.R.m) :
    ((fockDeg D n : ℤ) : ℚ) = ∑ τ, (∑ a : Fin (D.R.sigW n).1, |DV.aPlusQ D n τ a| +
      ∑ c : Fin (D.R.sigW n).2, |DV.aMinusQ D n τ c|) := by
  unfold fockDeg
  push_cast
  refine Finset.sum_congr rfl fun τ _ => ?_
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [(h n h1 h2 τ).1 a]
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [(h n h1 h2 τ).2 c, abs_neg]

theorem fockDeg_eq {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z Z' : w.Lt)
    (h : DV.KapDef (w.D Z)) (h' : DV.KapDef (w.D Z')) (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ (w.D Z).R.m) :
    fockDeg (w.D Z) n = fockDeg (w.D Z') n := by
  have e := fockDeg_cast (w.D Z) h n h1 h2
  have e' := fockDeg_cast (w.D Z') h' n h1 h2
  exact_mod_cast e.trans e'.symm

theorem forcedContent_eq_over_same_choices : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z Z' : w.Lt), DV.KapDef (w.D Z) →
    DV.KapDef (w.D Z') → F0K K.s (w.D Z) = F0K K.s (w.D Z') := by
  intro K B f T w Z Z' h h'
  funext y j
  have hT : FTypeG (w.D Z) (j.1 + 1) = FTypeG (w.D Z') (j.1 + 1) := by
    unfold FTypeG
    rw [fockDeg_eq w Z Z' h h' (j.1 + 1) (Nat.succ_pos _) j.2]
  unfold F0K FK
  rw [hT]
  rfl

end GlobalTheory.Mem.Top.Bl.RowWt
