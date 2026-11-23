import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryPairAction

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeisThetaLaws

theorem heis_theta_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D), (∀ w f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (heisO ψ S T w f)) ∧ (∀ w w' f, heisO ψ S T w (heisO ψ S T w' f) = ψ (symplOH S T w w') • heisO ψ S T (w + w') f) ∧ ∀ g h x y, symplO S T (actO S T g h x) (actO S T g h y) = symplO S T x y :=
  fun D ψ hψ S T =>
    ⟨fun w _ hf => GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w,
      fun w w' f => GlobalTheory.WeilVacMove.heisO_heisO ψ S T w w' f,
      GlobalTheory.SymplOInv.symplO_actO D S T⟩

end GlobalTheory.HeisThetaLaws
