import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviElementPreservesWittColumnSpan
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_element_preserves_witt_column_span : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ {S : Finset (Fin r)}, (∀ k ∈ S, ∀ i, i ≤ k → i ∈ S) →
    ∀ {g : GAd σ J}, g ∈ levi σ J X Y S → ∀ k ∈ S,
    (matHom _ σ J g).1 *ᵥ (fun i => adMat F X i k) =
      (adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J g).1 * adMat F X) k k • (fun i => adMat F X i k) := by
  first | exact @GlobalTheory.IdTorus.levi_mulVec_col | exact GlobalTheory.IdTorus.levi_mulVec_col | (intros; apply GlobalTheory.IdTorus.levi_mulVec_col <;> assumption)
