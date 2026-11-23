import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSubgroupAdjointScalar
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_subgroup_adjoint_scalar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L → ∀ (a : GL (Fin n) (AF F ⊗[F] E)) (x : Matrix (Fin n) (Fin 1) E) (pL : Matrix (Fin 1) (Fin n) E), pL * x = 1 → ∀ k ∈ levelAll σ J L a, ∀ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J k).1 * adMat F x = l.1 • adMat F x → absE F E l = 1 := by
  first | exact @GlobalTheory.IwasawaTriv.absE_eigen_eq_one | exact GlobalTheory.IwasawaTriv.absE_eigen_eq_one | (intros; apply GlobalTheory.IwasawaTriv.absE_eigen_eq_one <;> assumption)
