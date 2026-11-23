import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinResidueLine
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ResLine.Swap

section Swap

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField F] [NumberField E] in
theorem cT_add' (σ : E →ₐ[F] E) {a b : Type} (M N : Matrix a b E) :
    Formalism.UG.cT (σ : E →+* E) (M + N) = Formalism.UG.cT (σ : E →+* E) M + Formalism.UG.cT (σ : E →+* E) N := by
  ext i j; simp [Formalism.UG.cT]

omit [NumberField F] [NumberField E] in
theorem cT_sub' (σ : E →ₐ[F] E) {a b : Type} (M N : Matrix a b E) :
    Formalism.UG.cT (σ : E →+* E) (M - N) = Formalism.UG.cT (σ : E →+* E) M - Formalism.UG.cT (σ : E →+* E) N := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_cT_of_isCMExt {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {a b : Type} (M : Matrix a b E) :
    Formalism.UG.cT (σ : E →+* E) (Formalism.UG.cT (σ : E →+* E) M) = M := by
  ext i j; simp [Formalism.UG.cT, GlobalTheory.SiegelSet.sigma_sigma hσ]

omit [NumberField F] [NumberField E] in
theorem cT_eq_of_isHermND {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) :
    Formalism.UG.cT (σ : E →+* E) J = J := by
  ext i j; simpa [Formalism.UG.cT] using hJ.1 i j

end Swap

end GlobalTheory.ResLine.Swap

end
