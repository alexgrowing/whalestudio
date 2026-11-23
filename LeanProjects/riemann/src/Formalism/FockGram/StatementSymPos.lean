import Formalism.FockGram.StatementFock

open Matrix
open scoped ComplexOrder

noncomputable section

namespace Formalism.E

def SymGramPosSemidef : Prop :=
  ∀ (𝕜 σ : Type) [RCLike 𝕜] [Fintype σ] [DecidableEq σ] (a : ℕ) (G : Matrix σ σ 𝕜),
    G.PosSemidef → (symGram a G).PosSemidef

def SymGramPosDef : Prop :=
  ∀ (𝕜 σ : Type) [RCLike 𝕜] [Fintype σ] [DecidableEq σ] (a : ℕ) (G : Matrix σ σ 𝕜),
    G.PosDef → (symGram a G).PosDef

end Formalism.E
