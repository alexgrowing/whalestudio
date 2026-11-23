import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Transport

def CongAt (B : Base) {a b : ℕ} (P : HeightOneSpectrum (𝓞 B.host.E)) (M₀ : ℕ) (y : TC.GA B a) (y' : TC.GA B b)
    (x x₀ : Formalism.L2.Col.HomE B.fields.E a b) : Prop :=
  ∀ r s, Valued.v (adAt B.host.F P
    ((HMul.hMul (HMul.hMul ((y'⁻¹ : TC.GA B b).1 : Matrix (Fin b) (Fin b) (Formalism.L2.DIV.AfE B.host.F B.host.E))
      ((LinearMap.toMatrix' x).map (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) : Matrix (Fin b) (Fin a) (Formalism.L2.DIV.AfE B.host.F B.host.E)))
      (y.1 : Matrix (Fin a) (Fin a) (Formalism.L2.DIV.AfE B.host.F B.host.E)) -
      ((LinearMap.toMatrix' x₀).map (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) : Matrix (Fin b) (Fin a) (Formalism.L2.DIV.AfE B.host.F B.host.E))) r s)) ≤
    Valued.v ((M₀ : ℕ) : P.adicCompletion B.host.E)

end GlobalTheory.Transport
