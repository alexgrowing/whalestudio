import Formalism.LocalToGlobal.Columns.ReferenceKernelEquivOfLastComponent
import Formalism.LocalToGlobal.Columns.ChainOneB
import Formalism.LocalToGlobal.Columns.RecLevelSym

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

def FixESym : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (m2 : ℕ), R.m = m2 + 2 → FixE (R := R) (colLevSym Ch) m2

def OcbLevIsSym : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (m2 : ℕ), R.m = m2 + 2 → OcbLevIs Ch (colLevSym Ch) m2

end Formalism.L2.Col
