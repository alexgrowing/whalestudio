import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.first_standard_pair_member_has_theta_function : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A WW : HSp D) (rA : Rig A) (rW : Rig WW) (ν : (AE D)ˣ →* Circle) (e : AE D) (S : Finset (Pl D.host.E)) (I : Ideal (𝓞 D.host.E)) (vac : WO A WW → ℂ), rA.Is → rW.Is → IsHeckeChar D ν → IsIdemSum e S → I ≠ ⊥ → IsVacO ψ θ (neg A) WW (fun τ => -rA.s τ) rW.s rA.Λ rW.Λ vac → ∃ f, IsThetaAt ψ (symplO (neg A) WW) (heisO ψ (neg A) WW) e (latO (neg A) WW rA.Λ rW.Λ fun _ => True) 1 vac (stdFst ν e I A WW rA.β rW.β) f ∧ IsThetaFunO ψ (neg A) WW f := by
  first | exact @GlobalTheory.Adopt.first_standard_pair_member_has_theta_function | exact GlobalTheory.Adopt.first_standard_pair_member_has_theta_function | (intros; apply GlobalTheory.Adopt.first_standard_pair_member_has_theta_function <;> assumption)
