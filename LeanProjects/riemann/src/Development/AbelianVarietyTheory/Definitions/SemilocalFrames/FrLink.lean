import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ColDict

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.UG NumberField IsDedekindDomain Matrix Formalism.L2.SG.HidaSetting Formalism.L2.SG.ColDict
open scoped TensorProduct

namespace GlobalTheory.St.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def Mq (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Submodule (𝓞 D.host.E) (Fin (D.R.N 0) → D.host.E) :=
  (VS D).L0.comap ((Fintype.linearCombination D.host.E (qFr wt)).restrictScalars (𝓞 D.host.E))

def embA (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F)
    (x : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) : VA X.B.I :=
  ∑ j, ιA.symm (x j) • qA X wt j

abbrev FrQ (D : D7) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Type :=
  AdFrame (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (hat D.host.F (Mq wt))
    (D.host.g 0 * D.host.g 1) D.R.k

def FrLink (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F) (Fr : FrQ D wt) : Prop :=
  Fr.eps = ιA X.ew ∧
  (∀ i, embA X wt ιA (Fr.b i) - X.B.I.fmat (X.xu u) *ᵥ X.bw i ∈ mL X.B.I X.B.g) ∧
  (∀ i, embA X wt ιA (Fr.bd i) - X.B.I.fmat (X.xu u) *ᵥ X.bwd i ∈ mL X.B.I X.B.g) ∧
  ∀ a, Fr.psi a = X.psiEf (ιA.symm a)

end GlobalTheory.St.G

end
