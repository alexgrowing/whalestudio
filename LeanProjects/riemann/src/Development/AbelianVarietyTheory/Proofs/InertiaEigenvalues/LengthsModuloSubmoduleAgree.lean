import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect

noncomputable section

namespace GlobalTheory.LenModAgree

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

theorem lenMod_eq {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (S H : Submodule O M) :
    BlochKatoDuality.lenMod S H = lenModN S H := by
  unfold BlochKatoDuality.lenMod lenModN
  have h := (LinearMap.quotientInfEquivSupQuotient S H).length_eq
  rw [← h]
  have e : Submodule.comap S.subtype S ⊓ Submodule.comap S.subtype H = Submodule.comap S.subtype H := by simp
  exact (Submodule.quotEquivOfEq _ _ e).length_eq

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem main : (∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (A H : Submodule O M), lenModN A H = BlochKatoDuality.lenMod A H) ∧ ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i)) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (e : ℕ), LocBoundP i w hw r Xs M e ↔ LocBound i w hw r Xs M e := by
  refine ⟨fun O M _ _ _ A H => (lenMod_eq A H).symm, ?_⟩
  intro D i w hw r Xs k M e
  unfold LocBoundP LocBound
  rw [lenMod_eq]

end GlobalTheory.LenModAgree
