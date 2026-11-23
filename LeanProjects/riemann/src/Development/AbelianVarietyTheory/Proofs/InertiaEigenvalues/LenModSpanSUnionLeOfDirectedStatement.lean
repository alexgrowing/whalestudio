import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenModSpanSUnionLeOfDirected
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocMulVec
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lenMod_span_sUnion_le_of_directed' : ∀ {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (S : Set (Set M)) (H : Submodule O M) (N : ℕ∞), (∀ A ∈ S, ∀ B ∈ S, ∃ C ∈ S, A ⊆ C ∧ B ⊆ C) → (∀ A ∈ S, BlochKatoDuality.lenMod (Submodule.span O A) H ≤ N) → BlochKatoDuality.lenMod (Submodule.span O (⋃₀ S)) H ≤ N := by
  first | exact @GlobalTheory.Pass.LocDirect.lenMod_span_sUnion_le_of_directed | exact GlobalTheory.Pass.LocDirect.lenMod_span_sUnion_le_of_directed | (intros; apply GlobalTheory.Pass.LocDirect.lenMod_span_sUnion_le_of_directed <;> assumption)
