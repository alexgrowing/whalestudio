import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IdxRatioConjOfUnimod
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApprox

noncomputable section

namespace Formalism.L2.SG.Pf.ProdE

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem prodE_CZ_of_approxC (hap : ApproxC M δ u u' F0 what₂) (hst : Formalism.L2.SG.Pf.ProdEP2Cut.StepsU M δ u u' F0 what₂) :
    Formalism.L2.SG.Pf.ZsVolCut.ProdE M δ u u' F0 what₂ (Formalism.L2.SG.Pf.ZsVolCut.CZ M δ u u') :=
  prodE_of M δ u u' F0 what₂ hap (Formalism.L2.SG.Pf.ProdEP2Cut.locIdxC_of_count M δ u u' F0 what₂ hst)

theorem prodE_of_steps (hst : Formalism.L2.SG.Pf.ProdEP2Cut.StepsU M δ u u' F0 what₂) :
    Formalism.L2.SG.Pf.ZsVolCut.ProdE M δ u u' F0 what₂ (Formalism.L2.SG.Pf.ZsVolCut.CZ M δ u u') :=
  prodE_CZ_of_approxC M δ u u' F0 what₂ (Formalism.L2.SG.Pf.ProdEApprox.approxC M δ u u' F0 what₂) hst

end Formalism.L2.SG.Pf.ProdE
