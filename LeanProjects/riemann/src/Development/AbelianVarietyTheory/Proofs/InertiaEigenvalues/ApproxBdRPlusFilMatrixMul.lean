import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem use₁₀ : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (n d : ℕ) (X Z : Matrix (Fin d) (Fin d) (Per.BdRp l)), (∃ (k : ℕ) (s : Matrix (Fin d) (Fin d) bk.S), ∀ i j, aDp l (bk.ev (s i j)) - (l : Per.BdRp l) ^ k * X i j ∈ Per.FilP l n) → (∃ (k : ℕ) (s : Matrix (Fin d) (Fin d) bk.S), ∀ i j, aDp l (bk.ev (s i j)) - (l : Per.BdRp l) ^ k * Z i j ∈ Per.FilP l n) → ∃ (k : ℕ) (s : Matrix (Fin d) (Fin d) bk.S), ∀ i j, aDp l (bk.ev (s i j)) - (l : Per.BdRp l) ^ k * (X * Z) i j ∈ Per.FilP l n := by
  intro l _ K bk n d X Z ⟨k₁, s₁, h₁⟩ ⟨k₂, s₂, h₂⟩
  refine ⟨k₁ + k₂, s₁ * s₂, fun i j => ?_⟩
  have e : aDp l (bk.ev ((s₁ * s₂) i j)) - (l : Per.BdRp l) ^ (k₁ + k₂) * (X * Z) i j
      = ∑ m, (aDp l (bk.ev (s₁ i m)) * (aDp l (bk.ev (s₂ m j)) - (l : Per.BdRp l) ^ k₂ * Z m j)
        + (aDp l (bk.ev (s₁ i m)) - (l : Per.BdRp l) ^ k₁ * X i m) * ((l : Per.BdRp l) ^ k₂ * Z m j)) := by
    rw [Matrix.mul_apply, Matrix.mul_apply, map_sum, map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul, map_mul, pow_add]
    ring
  rw [e]
  exact Ideal.sum_mem _ fun m _ => Ideal.add_mem _ (Ideal.mul_mem_left _ _ (h₂ m j)) (Ideal.mul_mem_right _ _ (h₁ i m))

end GlobalTheory
