import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousLvMat

noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open Formalism.UG (cT bc)
open scoped TensorProduct NNReal

namespace GlobalTheory.SphEis.Inhabitant

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n j m : ℕ} {J : Matrix (Fin n) (Fin n) E} {C D : Matrix (Fin n) (Fin j) E}
  {Z : Matrix (Fin n) (Fin m) E} {J₀ : Matrix (Fin m) (Fin m) E}

theorem existsUnique_isLv (f : Fr σ J C D Z J₀) :
    ∃ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv ∧ Function.Injective lv ∧
      ∀ lv', IsLv σ J C D Z lv' → lv' = lv :=
  ⟨SphEisModel.lv f, SphEisModel.isLv_lv f, SphEisModel.isLv_injective f (SphEisModel.isLv_lv f),
    fun _ h => SphEisModel.isLv_unique f h (SphEisModel.isLv_lv f)⟩

theorem all_inhabited : ∃ (F E : Type) (_ : Field F) (_ : NumberField F) (_ : Field E) (_ : NumberField E) (_ : Algebra F E)
    (σ : E →ₐ[F] E) (J : Matrix (Fin 3) (Fin 3) E) (C D Z : Matrix (Fin 3) (Fin 1) E) (J₀ : Matrix (Fin 1) (Fin 1) E)
    (l : GL (Fin 1) (AF F ⊗[F] E) →* GAd σ J) (u : GAd σ J) (c : Matrix (Fin 1) (Fin 1) (AF F ⊗[F] E)),
    Fr σ J C D Z J₀ ∧ IsLv σ J C D Z l ∧ Function.Injective l ∧ Crd σ J C D Z J₀ u 1 c ∧ u ∈ fixG σ J C :=
  SphEisModel.inhabited

end GlobalTheory.SphEis.Inhabitant

end
