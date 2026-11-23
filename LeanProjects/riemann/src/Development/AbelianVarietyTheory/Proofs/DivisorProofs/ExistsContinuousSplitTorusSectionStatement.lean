import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousSplitTorusSection
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_split_torus_section : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∃ t : (Fin r → (AF F ⊗[F] E)ˣ) → GAd σ J, Continuous t ∧ ∀ l, IsIdTorusElt σ J X Y l (t l) := by
  first | exact @GlobalTheory.IdTorus.exists_continuous_isIdTorusElt | exact GlobalTheory.IdTorus.exists_continuous_isIdTorusElt | (intros; apply GlobalTheory.IdTorus.exists_continuous_isIdTorusElt <;> assumption)
