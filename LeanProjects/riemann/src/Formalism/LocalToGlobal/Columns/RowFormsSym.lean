import Formalism.LocalToGlobal.Columns.RowForms
import Formalism.LocalToGlobal.Columns.LevGSym

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section RBlockSym

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)

def rPsymF : LevFam X.E X.K R.r Pr.vGs := fun w =>
  ⟨HPsymF (𝓞 X.E ⧸ w.1.asIdeal) R.r R.k R.rS, chiSymF (Ch.psi0 w) R.r R.k R.rS⟩

theorem rowTyG_PsymF_H (w : {w // w ∈ Pr.vGs}) :
    (rowTyG Ch (rPsymF Ch) w).H = HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N R.m - 1) R.k R.r R.t R.m R.rS (r_le_X' R) := rfl

end RBlockSym

end Formalism.L2.Col
