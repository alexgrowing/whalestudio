import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsPermOfMin
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IsomFixOfExpOf

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G8

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

theorem glueProd_of_iso (h1 : JordanExists) (h2 : JordanInv) (h6 : GlueLoc) (hI : IsomFixOfExp) :
    GlueProd := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc hpos M hM Λ₀ hΛ₀ T hT
  refine ⟨⟨genus_of_fib h1 h2 h6 hI hK hF hs hnd hUc hpos hM hΛ₀ hT, fun hg 𝔭 h𝔭 =>
    fibP_ne_zero_of_genus hF hs hnd hUc hM hΛ₀ hg h𝔭⟩, card_glue hK hF hUc hM hΛ₀ hT⟩

end Formalism.L2.SG.Pf.G8

namespace Formalism.L2.SG.Pf.Cnt

theorem glueProd_of (h1 : JordanExists) (h2 : JordanInv) (h3 : JordanIsom) (h6 : GlueLoc) : GlueProd :=
  G8.glueProd_of_iso h1 h2 h6 (G8.isomFixOfExp_of h3)

end Formalism.L2.SG.Pf.Cnt
