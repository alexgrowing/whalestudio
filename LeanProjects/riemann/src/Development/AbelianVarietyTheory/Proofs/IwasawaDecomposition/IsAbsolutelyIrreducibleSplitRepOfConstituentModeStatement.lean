import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAbsolutelyIrreducibleSplitRepOfConstituentMode
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitRep
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAbsolutelyIrreducibleSplitRep_of_constituent_models : ∀ {k Γ L : Type} [Field k] [Group Γ] [Field L] [IsAlgClosed L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k), (∀ V, IsIrrSub (mapRep f ρ) V → ∃ (b : ℕ) (σ : Γ →* GL (Fin b) k) (C : Matrix (Fin a) (Fin b) L), Function.Injective C.mulVec ∧ LinearMap.range C.mulVecLin = V ∧ ∀ g, ((mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * C = C * ((mapRep f σ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L)) → GlobalTheory.SplitCoef.SplitRep ρ := by
  first | exact @GlobalTheory.SplitCrit.splitRep_of_models | exact GlobalTheory.SplitCrit.splitRep_of_models | (intros; apply GlobalTheory.SplitCrit.splitRep_of_models <;> assumption)
