import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitHeckeElementLabelZerosThenNegOnes
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_hecke_element_label_zeros_then_neg_ones : ∀ {D : D7} (V : HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i : ok × ℕ) (x : Bridge.Gf V), (i.2 ≤ V.rank → isTEnv V pl ok i x → IsLabElt V (pl i.1) (splitLab V.rank i.2) x) ∧ (isLocEnv V pl ok i x → IsLocElt V (pl i.1) x) ∧ (splitLab V.rank i.2).Pairwise (fun a b => b ≤ a) := by
  first | exact @GlobalTheory.Hk3Split.isLabElt_of_isTEnv | exact GlobalTheory.Hk3Split.isLabElt_of_isTEnv | (intros; apply GlobalTheory.Hk3Split.isLabElt_of_isTEnv <;> assumption)
