import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusElementMul
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_torus_element_mul : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, ∀ {l l' : Fin r → (AF F ⊗[F] E)ˣ} {a b : GAd σ J}, IsIdTorusElt σ J X Y l a → IsIdTorusElt σ J X Y l' b → IsIdTorusElt σ J X Y (l * l') (a * b) := by
  first | exact @GlobalTheory.IdTorus.isIdTorusElt_mul | exact GlobalTheory.IdTorus.isIdTorusElt_mul | (intros; apply GlobalTheory.IdTorus.isIdTorusElt_mul <;> assumption)
