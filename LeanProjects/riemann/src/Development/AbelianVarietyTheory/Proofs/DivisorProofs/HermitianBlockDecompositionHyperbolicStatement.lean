import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianBlockDecompositionHyperbolic
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_block_decomposition_hyperbolic : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n₁ d : ℕ)
    (G : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) E) (J₁ : Matrix (Fin n₁) (Fin n₁) E) (K : Matrix (Fin d) (Fin d) E),
    (∀ i i', G (Fin.castAdd 2 i) (Fin.castAdd 2 i') = J₁ i i') → (∀ i t, G (Fin.castAdd 2 i) (Fin.natAdd n₁ t) = 0) →
    (∀ t i, G (Fin.natAdd n₁ t) (Fin.castAdd 2 i) = 0) → G (Fin.natAdd n₁ 0) (Fin.natAdd n₁ 0) = 0 →
    G (Fin.natAdd n₁ 1) (Fin.natAdd n₁ 1) = 0 → G (Fin.natAdd n₁ 0) (Fin.natAdd n₁ 1) = 1 →
    G (Fin.natAdd n₁ 1) (Fin.natAdd n₁ 0) = 1 →
    ∀ z z' : Matrix (Fin (n₁ + 2)) (Fin d) (AE F E),
      symp (R := AF F) (cA σ) (-1) (incM F G) (incM F K) z z' =
        symp (R := AF F) (cA σ) (-1) (incM F J₁) (incM F K) (Matrix.of fun i l => z (Fin.castAdd 2 i) l)
          (Matrix.of fun i l => z' (Fin.castAdd 2 i) l) +
        Algebra.trace (AF F) (AE F E) (-∑ j, ∑ l, z (Fin.natAdd n₁ 0) j * incM F K j l * cA σ (z' (Fin.natAdd n₁ 1) l)) +
        Algebra.trace (AF F) (AE F E) (-∑ j, ∑ l, z (Fin.natAdd n₁ 1) j * incM F K j l * cA σ (z' (Fin.natAdd n₁ 0) l)) := by
  first | exact @GlobalTheory.symp_split_hyperbolic_plane | exact GlobalTheory.symp_split_hyperbolic_plane | (intros; apply GlobalTheory.symp_split_hyperbolic_plane <;> assumption)
