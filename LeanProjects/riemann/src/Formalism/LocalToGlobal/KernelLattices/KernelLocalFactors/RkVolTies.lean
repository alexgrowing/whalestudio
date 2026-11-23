import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData
import Formalism.LocalToGlobal.KernelLattices.ColumnData.AmbOfENeSd
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker.Cd

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.Col

variable {D : Car} {X : Fields}

def Seam.push (s : Seam D X) {a b : ℕ} (F : VCx X.Tau a b → ℂ) : TaylorLogMetric.VC D a b → ℂ := fun z => F fun τ => z (s.iT τ)

def Seam.pt (s : Seam D X) {a b : ℕ} (t : VCx X.Tau a b) : TaylorLogMetric.VC D a b := fun τ => t (s.iT.symm τ)

variable (s : Seam D X) {a b : ℕ}

end Formalism.L2.Ker.Cd
