import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodLocalGroupsNormalFramesSplitPlace
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodLocalGroups_normalFrames_splitPlace : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ), (∀ (J : JacLev D ρ) (s hh : k) (F₀ : Frame k J.W₀.rank n) (F : Frame k J.W.rank (n ⊕ Fin c)) (gl : GL (n ⊕ Fin c) k →* GA D J.W), 1 ≤ ρ → s ≠ 0 → hh ≠ 0 → (ofSplit q).IsJacFrame J s hh F₀ F → (∀ g, (ofSplit q).IsLoc F (gl g) g) → (∀ g, gl g ∈ jacGrp J.d ↔ g ∈ RFJ k n c ρ) ∧ ∀ g, ∀ y ∈ GlobalTheory.FinPl.grpOff J.W (· = q.v), gl g * y ∈ jacGrp J.d → gl g ∈ jacGrp J.d) ∧ ∀ (B : BesLev D ρ) (s : k) (FA : Frame k B.A.rank n) (F : Frame k B.V.rank (n ⊕ Fin c)) (gl : GL (n ⊕ Fin c) k →* GA D B.V), s ≠ 0 → (ofSplit q).IsBesFrame B s FA F → (∀ g, (ofSplit q).IsLoc F (gl g) g) → (∀ g, gl g ∈ besGrp B.d B.o ↔ g ∈ R k n c (ρ + 1)) ∧ ∀ g, ∀ y ∈ GlobalTheory.FinPl.grpOff B.V (· = q.v), gl g * y ∈ besGrp B.d B.o → gl g ∈ besGrp B.d B.o := by
  first | exact @GlobalTheory.LocGrpIff.local_groups_iff | exact GlobalTheory.LocGrpIff.local_groups_iff | (intros; apply GlobalTheory.LocGrpIff.local_groups_iff <;> assumption)
