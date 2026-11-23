import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftSL

noncomputable section

open scoped MatrixGroups Matrix
open Filter
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV

namespace GlobalTheory.K4

open GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def chiK (l : ℕ) [Fact l.Prime] (ψ : ZMod l → Qbar l) (r : ℕ) (y : (ZMod (l ^ r))ˣ) : Qbar l :=
  ψ (((y : ZMod (l ^ r)).val : ℕ) : ZMod l)

def ykA (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (pr : X.Fn l → Fin 2 → Qbar l) (W : GlobalTheory.Ord2.R2 Ω l)
    (N : ℕ) [NeZero N] (x : ZMod N) (c d k e : ℕ) (g : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (s : Ω ≃ₐ[ℚ] Ω) :
    Fin 2 → Qbar l :=
  limUnder atTop fun r : ℕ =>
    GlobalTheory.KA.spec (fun y : (ZMod (l ^ r))ˣ => ((((y : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r y)
      (Yk4 X l pr W r r N x c d k g) s

end GlobalTheory.K4
