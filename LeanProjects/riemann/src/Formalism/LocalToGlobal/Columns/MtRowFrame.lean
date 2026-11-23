import Formalism.LocalToGlobal.Columns.MtRowRep
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedRowLoc

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions

namespace Formalism.L2.Col

def rowFrameOf (D : D7) (Occ : Set (NG.FinTyp D.host.E D.R.r)) (e : D.what₂.FT ≃ FinTypCls Occ) : Formalism.L2.RowFrame D where
  rep σ := finTypRep Occ (e σ)
  inj _ _ h := e.injective (finTypRep_inj h)

end Formalism.L2.Col
