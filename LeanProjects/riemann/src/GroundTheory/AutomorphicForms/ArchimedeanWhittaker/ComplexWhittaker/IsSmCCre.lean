import Mathlib
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.ComplexWhittaker.InstMeasurableSpaceU2

namespace GroundTheory.Automorphic.ArchWhittakerC

open Matrix Complex
open scoped Matrix.Norms.L2Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (σ : UnitaryRep GL2C H)

noncomputable abbrev πC : BanachRep GL2C H := BanachRep.ofUnitary σ

abbrev IsSmC (v : H) : Prop := hGL2C.IsSmoothVector (πC σ) v

noncomputable abbrev dπC (X : gl2C) (v : H) : H := hGL2C.derivOp (πC σ) X v

theorem isSmC_dπC {v : H} (hv : IsSmC σ v) (X : gl2C) : IsSmC σ (dπC σ X v) :=
  hGL2C.isSmoothVector_derivOp (πC σ) hv X

noncomputable def Eop (v : H) : H := (1 / 2 : ℂ) • (dπC σ lK0 v - I • dπC σ lK1 v)

noncomputable def Fop (v : H) : H := -(1 / 2 : ℂ) • (dπC σ lK0 v + I • dπC σ lK1 v)

noncomputable def eU (a b : Fin 2) : gl2C := ⟨Matrix.single a b 1, Submodule.mem_top⟩

noncomputable def eUi (a b : Fin 2) : gl2C := ⟨Matrix.single a b I, Submodule.mem_top⟩

noncomputable def Cre (v : H) : H :=
  ∑ a : Fin 2, ∑ b : Fin 2,
    (dπC σ (eU a b) (dπC σ (eU b a) v) - dπC σ (eUi a b) (dπC σ (eUi b a) v))

noncomputable def Cim (v : H) : H :=
  ∑ a : Fin 2, ∑ b : Fin 2,
    (dπC σ (eU a b) (dπC σ (eUi b a) v) + dπC σ (eUi a b) (dπC σ (eU b a) v))

end GroundTheory.Automorphic.ArchWhittakerC
