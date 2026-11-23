import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameFunctionActionHolomorphicExtremalLowest
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolRepOfIsTau
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameFunctionAction_holomorphic_extremal_lowest : ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n), IsHolFam (fun _ => allPos n) fockL (vact lam) ∧ IsBotFam (fun _ => allPos n) (vact lam) (fun τ j => -((lam τ).w j : ℝ)) (ten fun τ => extremal ℂ n (lam τ)) ∧ (ten fun τ => extremal ℂ n (lam τ)) ≠ 0 ∧ (ten fun τ => extremal ℂ n (lam τ)) ∈ VV ℂ lam := by
  first | exact @GlobalTheory.JointHarm.vact_isHolFam_isBotFam | exact GlobalTheory.JointHarm.vact_isHolFam_isBotFam | (intros; apply GlobalTheory.JointHarm.vact_isHolFam_isBotFam <;> assumption)
