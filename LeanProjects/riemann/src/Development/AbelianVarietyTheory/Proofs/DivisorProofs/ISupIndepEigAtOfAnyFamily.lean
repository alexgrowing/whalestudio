import Mathlib
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col

namespace GlobalTheory

theorem iSupIndep_eigAt_of_any_family (K V I : Type) [Field K] [AddCommGroup V] [Module K V]
    (op : I → Module.End K V) : iSupIndep (eigAt op) :=
  iSupIndep.iInf (fun i (a : K) => (op i).maxGenEigenspace a)
    (fun i => Module.End.independent_maxGenEigenspace (op i))

end GlobalTheory
