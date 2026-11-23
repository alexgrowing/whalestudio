import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicPointUnitaryGroupGramOne

noncomputable section

open NumberField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta

namespace GlobalTheory.NormDictEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IsStdEmb {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (ι : Formalism.MainNotions.StandardLatticesGL3.GA D n →* GA D V) : Prop :=
  ∀ x, ι x ∈ GfC V ∧ ∀ i j, (finHom V (ι x)).1 i j = GlobalTheory.BotFormula.toAfE D (x.1.1 (Fin.cast hn i) (Fin.cast hn j))

end GlobalTheory.NormDictEx
