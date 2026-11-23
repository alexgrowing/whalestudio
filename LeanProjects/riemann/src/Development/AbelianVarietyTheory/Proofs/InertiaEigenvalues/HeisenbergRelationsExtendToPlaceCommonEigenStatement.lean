import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeisenbergRelationsExtendToPlaceCommonEigen
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankWeightComponentEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergRelations_extend_to_place_commonEigen : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Sb : Finset (FinPl D)) (v : FinPl D), v ∈ Sb → ∀ (p f : WO S T → ℂ), (∀ u, IsHalf (idem D (.inl v)) u → CoEig ψ S T p f u ∨ ∃ l, IsHalf (idem D (.inl v)) l ∧ CoEig ψ S T p f l ∧ ψ (symplO S T l u) ≠ 1) → RelOff ψ S T Sb p f → RelOff ψ S T (dropPl Sb v) p f := by
  first | exact @GlobalTheory.DownLift.GenSplit.relOff_dropPl_of_coEig | exact GlobalTheory.DownLift.GenSplit.relOff_dropPl_of_coEig | (intros; apply GlobalTheory.DownLift.GenSplit.relOff_dropPl_of_coEig <;> assumption)
