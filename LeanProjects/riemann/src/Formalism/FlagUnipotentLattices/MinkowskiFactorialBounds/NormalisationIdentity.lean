import Formalism.FlagUnipotentLattices.UnipotentStabiliserCharacterisation

namespace Formalism.HermitianLatticeCounting.P
open Finset Formalism.HermitianLatticeCounting.ExpansionTerms

noncomputable def brG (c : ℝ) (j : ℕ) : ℝ := if j = 0 then 2 + c else 1 + 1 / (j : ℝ)

end Formalism.HermitianLatticeCounting.P
