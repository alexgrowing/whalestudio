import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdeleComponentAtFinitePlaceIntegralMemLocalTenso
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SigV
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adeleComponentAtFinitePlace_integral_mem_localTensor : ∀ (D : D7) (v : Pl D) (a : AE D), a ∈ intAt D (· = v) → compAt D v a ∈ intV D v := by
  first | exact @GlobalTheory.FixedUnitNorm.compAt_mem_intV_of_intAt | exact GlobalTheory.FixedUnitNorm.compAt_mem_intV_of_intAt | (intros; apply GlobalTheory.FixedUnitNorm.compAt_mem_intV_of_intAt <;> assumption)
