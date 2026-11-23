import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelIndexLevelUnipotentCoprimePrime
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecomposition
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.L2
open Formalism.AUTREP (GAf)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_levelUnipotent_coprime_prime : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (r p : ℕ) (H : Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))), p.Prime → s.Above p → r ≤ n → (∀ g, g ∈ H ↔ NG.UniRT s r g) → Nat.Coprime (H.relIndex (Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring)) p := by
  first | exact @GlobalTheory.UniLevelIndex.relIndex_coprime | exact GlobalTheory.UniLevelIndex.relIndex_coprime | (intros; apply GlobalTheory.UniLevelIndex.relIndex_coprime <;> assumption)
