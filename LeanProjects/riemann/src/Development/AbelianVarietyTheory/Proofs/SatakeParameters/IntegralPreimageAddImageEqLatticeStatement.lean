import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralPreimageAddImageEqLattice
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_preimage_add_image_eq_lattice : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n n' : ℕ) (x : Matrix (Fin n') (Fin n) L) (y : Matrix (Fin n) (Fin n') L),
    ∃ a : GL (Fin n) L, ∀ v : Fin n → L,
      (∃ u : Fin n → L, ∃ w : Fin n' → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) ∧ (∀ i, w i ∈ Formalism.UG.intL L) ∧ v = u + y *ᵥ w) ↔
        ∃ t : Fin n → L, (∀ i, t i ∈ Formalism.UG.intL L) ∧ v = (a : Matrix (Fin n) (Fin n) L) *ᵥ t := by
  first | exact @GlobalTheory.Hk3.HoweG.latA_basis | exact GlobalTheory.Hk3.HoweG.latA_basis | (intros; apply GlobalTheory.Hk3.HoweG.latA_basis <;> assumption)
