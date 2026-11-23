import Formalism.FrobeniusContraction.StatementTop

namespace Formalism.WachCohomologyFacts.PLemmaS

open Formalism.WachCohomologyFacts.Top

def lift (ℓ : ℕ) (a : ℤ) (x : ZMod ℓ) : ℤ := ((x - (a : ZMod ℓ)).val : ℤ) + a

end Formalism.WachCohomologyFacts.PLemmaS
