import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitElementIsTorusElement
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_element_is_torus_element : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (u : Fin r → ℝ) {a : GAd σ J}, IsSplitElt σ J X Y S u a → IsIdTorusElt σ J X Y (fun k => archUnit F E (stepSum S u k)) a := by
  first | exact @GlobalTheory.IdTorus.isIdTorusElt_of_isSplitElt | exact GlobalTheory.IdTorus.isIdTorusElt_of_isSplitElt | (intros; apply GlobalTheory.IdTorus.isIdTorusElt_of_isSplitElt <;> assumption)
