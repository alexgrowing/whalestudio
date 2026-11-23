import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut

noncomputable section

namespace Formalism.L2.S.S7.GLOne

open NumberField
open scoped TensorProduct
open Formalism.MainNotions.S

variable (I : AutInst)

abbrev AEf : Type := I.E ⊗[I.F] Af I.F

abbrev GLf (j : ℕ) : Type := GL (Fin j) (AEf I)

abbrev GLinf (j : ℕ) : Type := InfinitePlace I.F → GL (Fin j) ℂ

abbrev GLA (j : ℕ) : Type := GLinf I j × GLf I j

def ratGL (j : ℕ) : GL (Fin j) I.E →* GLA I j :=
  MonoidHom.prod (MonoidHom.pi fun v => Matrix.GeneralLinearGroup.map (I.φ v))
    (Matrix.GeneralLinearGroup.map (Formalism.UG.inclE (F := I.F) (Af I.F)))

def idl (u : (AEf I)ˣ) : Submodule (𝓞 I.E) I.E :=
  Submodule.span (𝓞 I.E)
    {e : I.E | ((u⁻¹ : (AEf I)ˣ) : AEf I) * Formalism.UG.inclE (F := I.F) (Af I.F) e ∈ IntAf I.F I.E}

open Classical in

def nrmF (u : (AEf I)ˣ) : ℝ :=
  if h : IsFractional (nonZeroDivisors (𝓞 I.E)) (idl I u) then
    ((FractionalIdeal.absNorm (⟨idl I u, h⟩ : FractionalIdeal (nonZeroDivisors (𝓞 I.E)) I.E) : ℚ) : ℝ)⁻¹
  else 0

def detNorm {j : ℕ} (m : GLA I j) : ℝ :=
  nrmF I (Matrix.GeneralLinearGroup.det m.2) *
    ∏ v, ‖((Matrix.GeneralLinearGroup.det (m.1 v) : ℂˣ) : ℂ)‖ ^ 2

end Formalism.L2.S.S7.GLOne

end
