import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeCosetTranslateMemOfCover
import Mathlib
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_coset_translate_mem_of_cover : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ (N : ℕ) (x : Matrix (Fin r ⊕ Fin t) (Fin r) K) (g : GL (Fin r) K) (z₀ : Matrix (Fin r ⊕ Fin t) (Fin r) O), x * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z₀).map (algebraMap O K) → (∀ z : Matrix (Fin r ⊕ Fin t) (Fin r) O, ∃ (g' : GL (Fin r) K) (z' : Matrix (Fin r ⊕ Fin t) (Fin r) O), (x + (ϖ ^ N • z).map (algebraMap O K)) * (g' : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z').map (algebraMap O K)) → ∀ z : Matrix (Fin r ⊕ Fin t) (Fin r) O, ∃ z' : Matrix (Fin r ⊕ Fin t) (Fin r) O, (x + (ϖ ^ N • z).map (algebraMap O K)) * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z').map (algebraMap O K) := by
  first | exact @GlobalTheory.coset_translate_mem_of_cover | exact GlobalTheory.coset_translate_mem_of_cover | (intros; apply GlobalTheory.coset_translate_mem_of_cover <;> assumption)
