import Formalism.LocalToGlobal.Columns.ChainOneB

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

def ocbBEnt {E : Type} [Field E] {N' N : ℕ} (n' n q : ℕ) (y : HomE E N' N) (l s : ℕ) : E :=
  Loc.atN (y (Loc.eN E N' s)) l * (q : E) ^ (LocE.scE n' (fun i => i + 1) s - LocE.scE n (fun i => i + 1) l)

theorem ocbBEnt_entB {E : Type} [Field E] [NumberField E] {N' N : ℕ} (q k₀ c' n' c n : ℕ) (y : HomE E N' N) (p p' : ℕ) :
    LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) y p p' = ocbBEnt n' n q y (LocE.fIdx k₀ c n p) (LocE.fIdx k₀ c' n' p') := rfl

end Formalism.L2.Col
