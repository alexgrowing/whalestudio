import Formalism.RealPlaceAnalysis.Complexify

noncomputable section

namespace Formalism.REAL

def UJEmb : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool),
    Topology.IsClosedEmbedding (fun g : UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
      Matrix (Fin n) (Fin n) ℂ)) ∧
    Set.range (fun g : UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) =
      {g | inUJ ε g}

def UJLocCompact : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), LocallyCompactSpace (UJ ε)

end Formalism.REAL
