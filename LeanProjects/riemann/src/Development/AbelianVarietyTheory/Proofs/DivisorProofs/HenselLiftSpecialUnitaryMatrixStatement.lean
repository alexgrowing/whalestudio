import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HenselLiftSpecialUnitaryMatrix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntLocConjIntLocConj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open scoped TensorProduct
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdelicU GlobalTheory.TamOne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hensel_lift_special_unitary_matrix : ∀ {R : Type} [CommRing R] (c : R →+* R), (∀ x, c (c x) = x) → ∀ (I : Ideal R), (∀ x ∈ I, c x ∈ I) → IsAdicComplete I R → ∀ w : R, w + c w = 1 → ∀ (r : ℕ) (g : Matrix (Fin r) (Fin r) R), (∀ a b, ((g.map c)ᵀ * g - 1) a b ∈ I) → g.det - 1 ∈ I → ∃ g' : Matrix (Fin r) (Fin r) R, (g'.map c)ᵀ * g' = 1 ∧ g'.det = 1 ∧ ∀ a b, g' a b - g a b ∈ I := by
  first | exact @GlobalTheory.HenselSU.hensel_special_unitary | exact GlobalTheory.HenselSU.hensel_special_unitary | (intros; apply GlobalTheory.HenselSU.hensel_special_unitary <;> assumption)
