import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecond
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaFunction_standardPairSecond : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A' WW : HSp D) (rA' : Rig A') (rW : Rig WW) (ν : (AE D)ˣ →* Circle) (e : AE D) (S : Finset (Pl D.host.E)) (I : Ideal (𝓞 D.host.E)) (a : ℕ) (vac : WO A' WW → ℂ), rA'.Is → rW.Is → IsHeckeChar D ν → IsIdemSum e S → I ≠ ⊥ → IsVacO ψ θ A' WW rA'.s rW.s rA'.Λ rW.Λ vac → ∃ f, IsThetaAt ψ (symplO A' WW) (heisO ψ A' WW) (cA D e) (latO A' WW rA'.Λ rW.Λ fun _ => True) 1 vac (stdSnd ν e I a A' WW rA'.β rW.β) f ∧ IsThetaFunO ψ A' WW f := by
  first | exact @GlobalTheory.CompanionTheory.StdSndTheta.exists_theta | exact GlobalTheory.CompanionTheory.StdSndTheta.exists_theta | (intros; apply GlobalTheory.CompanionTheory.StdSndTheta.exists_theta <;> assumption)
