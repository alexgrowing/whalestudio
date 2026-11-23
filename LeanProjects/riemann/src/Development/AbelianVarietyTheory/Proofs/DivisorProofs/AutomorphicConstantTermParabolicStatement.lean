import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicConstantTermParabolic
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphic_constant_term_parabolic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (C : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ), IsIsoCols σ J C → ∀ (H K : Subgroup (GAd σ J)) (φ c : GAd σ J → ℂ), ratPts σ J ⊓ parFlag σ J C d ≤ H → IsAutOn σ J H K φ → IsConstTermOn σ J (unipFlag σ J C d) φ c → IsAutOn σ J (leftGrp σ J C d) K c ∧ ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → IsConstTermOn σ J (unipFlag σ J C d) (l.foldr lineDer φ) (l.foldr lineDer c) := by
  first | exact @GlobalTheory.UAut.ConstAut.isAutOn_constTerm | exact GlobalTheory.UAut.ConstAut.isAutOn_constTerm | (intros; apply GlobalTheory.UAut.ConstAut.isAutOn_constTerm <;> assumption)
