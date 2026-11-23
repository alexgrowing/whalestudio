import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticePairVolumeBounds
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.RealPlaceAnalysis.Complexify
open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_pair_volume_bounds : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (a b : ℕ) (X : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ) (X' : InfinitePlace K → Matrix (Fin b) (Fin b) ℂ) (A : Submodule (𝓞 K) (Fin a → K)) (B : Submodule (𝓞 K) (Fin b → K)) (lo hi : ℝ), (∀ w, IsUnit (X w).det) → (∀ w, IsUnit (X' w).det) → A.FG → B.FG → Submodule.span K (A : Set (Fin a → K)) = ⊤ → Submodule.span K (B : Set (Fin b → K)) = ⊤ → 0 < lo → 0 < hi → (∀ N, N ≤ A → N ≠ ⊥ → lo ≤ size (Pi.basisFun K (Fin a)) X N) → largestSize (Pi.basisFun K (Fin b)) X' B ≤ hi → ∀ T : InfinitePlace K → Matrix (Fin b) (Fin a) ℂ, ∃ φ : Matrix (Fin b) (Fin a) K, (∀ y ∈ A, φ *ᵥ y ∈ B) ∧ Real.sqrt (∑ w, ∑ i, ∑ j, ‖(T w - (X' w)⁻¹ * φ.map w.embedding * X w) i j‖ ^ 2) ≤ (a : ℝ) * b * Real.sqrt (nPl K) * |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (nPl K : ℝ))) * hi / (2 * lo) := by
  first | exact @GlobalTheory.HomCover.exists_hom_near | exact GlobalTheory.HomCover.exists_hom_near | (intros; apply GlobalTheory.HomCover.exists_hom_near <;> assumption)
