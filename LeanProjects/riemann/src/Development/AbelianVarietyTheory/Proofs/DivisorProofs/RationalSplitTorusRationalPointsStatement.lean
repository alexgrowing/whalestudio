import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSplitTorusRationalPoints
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_split_torus_rational_points : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (e : Fin r → Eˣ) {a : GAd σ J}, IsIdTorusElt σ J X Y (fun k => Units.map (inclR (F := F) (AF F)).toMonoidHom (e k)) a → a ∈ ratPts σ J := by
  first | exact @GlobalTheory.IdTorus.mem_ratPts_of_isIdTorusElt | exact GlobalTheory.IdTorus.mem_ratPts_of_isIdTorusElt | (intros; apply GlobalTheory.IdTorus.mem_ratPts_of_isIdTorusElt <;> assumption)
