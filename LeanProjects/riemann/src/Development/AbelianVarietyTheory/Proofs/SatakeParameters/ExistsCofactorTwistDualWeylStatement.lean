import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCofactorTwistDualWeyl
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PosOkId
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cofactorTwist_dualWeyl : ∀ (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν → ν (Fin.last m) = 0 → ∀ f ∈ dualWeyl R (m + 1) (m + 1) ν, ∃ g ∈ dualWeyl R (m + 1) (m + 1) (nuDual ν), CofRel R m ν f g := by
  first | exact @GlobalTheory.ValCmp.exists_cofRel_dualWeyl | exact GlobalTheory.ValCmp.exists_cofRel_dualWeyl | (intros; apply GlobalTheory.ValCmp.exists_cofRel_dualWeyl <;> assumption)
