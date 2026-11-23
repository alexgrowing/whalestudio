import Mathlib
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.Uniqueness

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix
open scoped Matrix.Norms.L2Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def toTopRep (σ : UnitaryRep (GL (Fin 2) ℝ) H) : UnitaryRep FiltrationCocycleLiftCriterion H where
  toHom := σ.toHom.comp FiltrationCocycleLiftCriterion.subtype
  continuous_orbit' v := (σ.continuous_orbit v).comp continuous_subtype_val

@[simp] theorem toTopRep_apply (σ : UnitaryRep (GL (Fin 2) ℝ) H) (g : FiltrationCocycleLiftCriterion) :
    toTopRep σ g = σ (g : GL (Fin 2) ℝ) := rfl

noncomputable def upperUnipotent (x : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, x; 0, 1] (by simp)

abbrev SmoothVectorsGL2 (σ : UnitaryRep (GL (Fin 2) ℝ) H) : Type _ :=
  hGL2.SmoothFrechet (πσ (toTopRep σ))

noncomputable abbrev whittakerFunctionals (σ : UnitaryRep (GL (Fin 2) ℝ) H) (ψ : ℝ → ℂ) :
    Submodule ℂ (SmoothVectorsGL2 σ →L[ℂ] ℂ) :=
  whitSpace (toTopRep σ) ψ

end GroundTheory.Automorphic.ArchWhittaker
