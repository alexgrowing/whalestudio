import Formalism.LocalToGlobal.InertKernelTheory.DefsRep
import Formalism.LocalToGlobal.InertKernelTheory.DefsBeCob

noncomputable section

namespace Formalism.L2.KerInert.Rep

open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

def CurveDict : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ) (l : ℕ) [Fact l.Prime]
    (g : Formalism.MainNotions.GL3Theta.G1 l) (hLT : Formalism.L2.G.Pend.LTIso g),
    Formalism.MainNotions.GL3Theta.At D cc δ g → 5 ≤ l → Formalism.MainNotions.GL3Theta.InertK D l → Formalism.MainNotions.GL3Theta.ModelOverW g.lam g.abelian₂ g.C →
    ∃ g2 g3 ε s2 : MaximalUnramifiedExtension l, (g2 : ℂ_[l]) = Formalism.L2.Th1.A.g₂ g.W ∧ (g3 : ℂ_[l]) = Formalism.L2.Th1.A.g₃ g.W ∧
      (ε : ℂ_[l]) = (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹ ∧
      PowerSeries.rescale ((g.C.u⁻¹ : ℂ_[l]ˣ) : ℂ_[l]) (Formalism.MainNotions.TaylorLogMetric.sgSer g.lam g.abelian₂) =
        PowerSeries.C ((g.C.u⁻¹ : ℂ_[l]ˣ) : ℂ_[l]) * Formalism.L2.Th1.B.sgW g.W (s2 : ℂ_[l]) ∧
      ‖((g.C.u⁻¹ : ℂ_[l]ˣ) : ℂ_[l]) * (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹‖ = 1 ∧
      CurveAt l (Formalism.L2.G.Pend.beLT hLT) g2 g3 ε s2 ∧
      ∀ D' : Formalism.BasicNotions.D7, DictInt D' g.lam g.abelian₂
        (((g.C.u⁻¹ : ℂ_[l]ˣ) : ℂ_[l]) * (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹) g2 g3 s2 ε

end Formalism.L2.KerInert.Rep
