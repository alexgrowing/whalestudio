import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CofactorTwistRelationRowActEquivariant
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PosOkId
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cofactorTwistRelation_rowAct_equivariant : ∀ (K : Type) [Field K] (m : ℕ) (ν : Fin (m + 1) → ℕ) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) K), IsUnit h.det → ∀ f ∈ dualWeyl K (m + 1) (m + 1) ν, ∀ g : MP K (m + 1), CofRel K m ν f g → CofRel K m ν (rowAct K h⁻¹ f) (h.det ^ (-(ν 0 : ℤ)) • rowAct K h.transpose g) := by
  first | exact @GlobalTheory.ValCmp.Eqv.cofRel_rowAct | exact GlobalTheory.ValCmp.Eqv.cofRel_rowAct | (intros; apply GlobalTheory.ValCmp.Eqv.cofRel_rowAct <;> assumption)
