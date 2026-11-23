import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.ExistsDenOfIsCompact

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def orb {k : ℕ} (U : Subgroup (GL (Fin k) (AE F E))) : Submodule (SS F E) (Fin k → AE F E) :=
  Submodule.span (SS F E) {y | ∃ g ∈ U, ∃ j : Fin k,
    y = (g : Matrix (Fin k) (Fin k) (AE F E)) *ᵥ (Pi.single j 1 : Fin k → AE F E)}

end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

end
