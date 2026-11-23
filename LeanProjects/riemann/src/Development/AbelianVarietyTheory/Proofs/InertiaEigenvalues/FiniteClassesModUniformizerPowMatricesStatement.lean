import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesModUniformizerPowMatrices
import Mathlib
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_classes_mod_uniformizer_pow_matrices : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ N : ℕ, ∃ T : Finset (Matrix (Fin r ⊕ Fin t) (Fin r) K), ∀ (x : Matrix (Fin r ⊕ Fin t) (Fin r) K) (z : Matrix (Fin r ⊕ Fin t) (Fin r) O), algebraMap O K (ϖ ^ N) • x = z.map (algebraMap O K) → ∃ y ∈ T, ∃ z' : Matrix (Fin r ⊕ Fin t) (Fin r) O, x = y + (ϖ ^ N • z').map (algebraMap O K) := by
  first | exact @GlobalTheory.GenUnr.finite_classes_mod_pow | exact GlobalTheory.GenUnr.finite_classes_mod_pow | (intros; apply GlobalTheory.GenUnr.finite_classes_mod_pow <;> assumption)
