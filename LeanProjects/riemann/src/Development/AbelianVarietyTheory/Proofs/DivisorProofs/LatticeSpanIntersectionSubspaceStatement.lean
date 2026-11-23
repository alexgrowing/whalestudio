import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSpanIntersectionSubspace
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_span_intersection_subspace : ∀ (K : Type) [Field K] [NumberField K] (r : ℕ) (E : Submodule (𝓞 K) (Fin r → K)) (V : Submodule K (Fin r → K)), Submodule.span K (E : Set (Fin r → K)) = ⊤ → Submodule.span K ((E ⊓ V.restrictScalars (𝓞 K) : Submodule (𝓞 K) (Fin r → K)) : Set (Fin r → K)) = V := by
  first | exact @GlobalTheory.span_cut | exact GlobalTheory.span_cut | (intros; apply GlobalTheory.span_cut <;> assumption)
