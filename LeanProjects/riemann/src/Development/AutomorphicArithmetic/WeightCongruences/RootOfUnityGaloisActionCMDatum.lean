import Mathlib
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.KcEqOfPowEqOne

open NumberField Formalism.HC

theorem UpperTheory.rootOfUnity_galois_action_CMDatum :
    ∀ (φ : Frame) (H : HostAx φ) (z : H.E), (∃ m : ℕ, 0 < m ∧ z ^ m = 1) →
      H.gal.symm φ.iod z = z ∧ H.conj z = z⁻¹ ∧ H.gal.symm φ.sg z = z⁻¹ := by
  intro φ H z hz
  have C : HostCore H.toHostRaw := { H.der with }
  have h1 : H.gal.symm φ.iod z = z :=
    Der.kc_iod_fix H.toHostRaw C _ (H.gal.apply_symm_apply _) z hz
  have h2 : H.conj z = z⁻¹ :=
    eq_inv_of_mul_eq_one_right (Der.kc_conj_mul_self H.toHostRaw C z hz)
  refine ⟨h1, h2, ?_⟩
  rw [← φ.cc_mul_iod, map_mul, AlgEquiv.mul_apply, h1]
  exact h2
