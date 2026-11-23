import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.HRAddRight

noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem memA {a : ℕ} (X : lamA v Λ a) (i : Fin a) : (X : TupV (E := E) v n a) i ∈ latLoc (E := E) v Λ :=
  X.2 i

def cf (hSD : IsSDLoc σ J v Λ) {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e) {a : ℕ}
    (X : lamA v Λ a) (i : Fin a) (p : Fin n) : OR (E := E) v :=
  ⟨hR (Fv F v) σ J (e p) ((X : TupV (E := E) v n a) i), (hSD _).1 (memA v Λ X i) _ (bas_mem v Λ he p)⟩

theorem cf_coe (hSD : IsSDLoc σ J v Λ) {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e) {a : ℕ}
    (X : lamA v Λ a) (i : Fin a) (p : Fin n) :
    (cf σ J v Λ hSD he X i p : Fv F v ⊗[F] E) = hR (Fv F v) σ J (e p) ((X : TupV (E := E) v n a) i) := rfl

def phi (hSD : IsSDLoc σ J v Λ) {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e) {K : Type} [CommRing K]
    (π : OR (E := E) v →+* K) (a : ℕ) : lamA v Λ a →+ (Fin a → Fin n → K) where
  toFun X := fun i p => π (cf σ J v Λ hSD he X i p)
  map_zero' := by
    funext i p
    have h : cf σ J v Λ hSD he (0 : lamA v Λ a) i p = 0 := by
      apply Subtype.ext
      rw [cf_coe]
      simp [hR, hform]
    simp only [h, map_zero, Pi.zero_apply]
  map_add' X Y := by
    funext i p
    have h : cf σ J v Λ hSD he (X + Y) i p = cf σ J v Λ hSD he X i p + cf σ J v Λ hSD he Y i p := by
      apply Subtype.ext
      simp only [cf_coe, AddSubgroup.coe_add, Pi.add_apply, Subring.coe_add]
      exact hR_add_right σ J v _ _ _
    simp only [h, map_add, Pi.add_apply]

theorem phi_apply (hSD : IsSDLoc σ J v Λ) {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e) {K : Type}
    [CommRing K] (π : OR (E := E) v →+* K) {a : ℕ} (X : lamA v Λ a) (i : Fin a) (p : Fin n) :
    phi σ J v Λ hSD he π a X i p = π (cf σ J v Λ hSD he X i p) := rfl

end PI.OmLocU.Red
