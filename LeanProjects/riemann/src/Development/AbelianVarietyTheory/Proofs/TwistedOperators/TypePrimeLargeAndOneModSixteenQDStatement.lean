import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePrimeLargeAndOneModSixteenQD
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typePrime_large_and_one_mod_sixteen_q_d : ∀ (D : D7) (L : SizeData₂ D), ParameterChoice' D L → ∀ k : Fin 2, Module.finrank ℚ D.host.E * D.R.r + 1 < D.host.g k ∧ GlobalTheory.BadShare.PrimeOK (D.host.g k) D.host.q D.host.d := by
  first | exact @GlobalTheory.TypePrimeSize.typePrime_large_and_ok | exact GlobalTheory.TypePrimeSize.typePrime_large_and_ok | (intros; apply GlobalTheory.TypePrimeSize.typePrime_large_and_ok <;> assumption)
