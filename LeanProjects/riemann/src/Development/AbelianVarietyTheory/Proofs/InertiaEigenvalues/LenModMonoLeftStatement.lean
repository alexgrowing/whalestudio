import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenModMonoLeft
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocMulVec
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lenMod_mono_left' : ∀ {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (S S' H : Submodule O M), S ≤ S' → BlochKatoDuality.lenMod S H ≤ BlochKatoDuality.lenMod S' H := by
  first | exact @GlobalTheory.lenMod_mono_left | exact GlobalTheory.lenMod_mono_left | (intros; apply GlobalTheory.lenMod_mono_left <;> assumption)
