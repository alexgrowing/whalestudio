import Formalism.WachModuleLifts.Statement

open Finset

noncomputable section

namespace Formalism.CL

namespace CSharpOdd1

variable {p : ℕ} [hp : Fact p.Prime]

def Zp (p : ℕ) [Fact p.Prime] : Polynomial ℚ_[p] :=
  Polynomial.C ((p : ℚ_[p])⁻¹) * Polynomial.X ^ (p - 1) *
    (Polynomial.X + Polynomial.C (-(p : ℚ_[p])))

end CSharpOdd1

end Formalism.CL
