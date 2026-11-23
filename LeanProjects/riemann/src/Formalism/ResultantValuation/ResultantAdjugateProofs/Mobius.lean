import Formalism.ResultantValuation.SubspaceCount

noncomputable section

namespace Formalism.ResultantValuation

namespace QBinomialResultantAdjugate

def qb (q : ℤ) : ℕ → ℕ → ℤ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => qb q n k + q ^ (k + 1) * qb q n (k + 1)

end QBinomialResultantAdjugate

end Formalism.ResultantValuation
