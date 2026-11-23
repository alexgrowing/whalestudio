import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckePreservesGoodPart
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_preserves_good_part : ∀ (D : D7), CommG D → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k P, HkIdx i k P → ∀ x ∈ V0 D.nexp i j b, D.nexp.hkF i j b k P x ∈ V0 D.nexp i j b := by
  first | exact @GlobalTheory.HkGoodStable.hkF_mem_V0 | exact GlobalTheory.HkGoodStable.hkF_mem_V0 | (intros; apply GlobalTheory.HkGoodStable.hkF_mem_V0 <;> assumption)
