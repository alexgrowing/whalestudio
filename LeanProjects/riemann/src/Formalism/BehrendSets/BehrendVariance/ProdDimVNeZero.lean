import Formalism.BehrendSets.StatementE

open Finset Real

noncomputable section

namespace Formalism.BehrendSets.Count

def F (n : ℕ) : ℝ := ∑ i ∈ range n, Real.log ((i.factorial : ℕ) : ℝ)

end Formalism.BehrendSets.Count

namespace Formalism.BehrendSets

open Formalism.BehrendSets.Count

end Formalism.BehrendSets
