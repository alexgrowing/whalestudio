import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantOrbitOfInvPowCharacter
import Mathlib
import Formalism.CharacterColumnKernels.StatementRho
import Formalism.GaloisCohomology.LocalTateDualityK
import ReciprocityTheory.Hypotheses.GalCohDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyConstant_orbit_of_inv_pow_character' : ∀ {p : ℕ} {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] (ε : G →* Oˣ),
    (∀ N : ℕ, IsLocallyConstant (fun g : G => Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε g : Oˣ) : O))) →
    ∀ (e : ℕ) {M : Type} [AddCommGroup M] [Module O M] (ρ : Representation O G M),
    (∀ g m, ρ g m = ((((ε g) ^ e)⁻¹ : Oˣ) : O) • m) → ∀ (m : M) (N : ℕ), (p : O) ^ N • m = 0 →
    IsLocallyConstant (fun g => ρ g m) := by
  first | exact @GlobalTheory.ShapeNeg.isLocallyConstant_orbit_of_inv_pow_character | exact GlobalTheory.ShapeNeg.isLocallyConstant_orbit_of_inv_pow_character | (intros; apply GlobalTheory.ShapeNeg.isLocallyConstant_orbit_of_inv_pow_character <;> assumption)
