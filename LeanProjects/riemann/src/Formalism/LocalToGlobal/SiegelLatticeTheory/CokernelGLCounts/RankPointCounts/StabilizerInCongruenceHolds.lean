import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrameShapeHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolFin

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolOrb

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem stabilizer_in_congruence_holds : StabInCZ M δ u u' F0 what₂ :=
  Formalism.L2.SG.Pf.ZsVolIn.stabInCZ_of M δ u u' F0 what₂ (Formalism.L2.SG.Pf.ZsVolLat.frameShape_holds M δ u u' F0 what₂)

theorem orbStabE_of_act (h : OrbActE M δ u u' F0 what₂) : Formalism.L2.SG.Pf.ZsVolCut.OrbStabE M δ u u' F0 what₂
    (Formalism.L2.SG.Pf.ZsVolCut.CZ M δ u u') :=
  orbStabE_of M δ u u' F0 what₂ (stabilizer_in_congruence_holds M δ u u' F0 what₂) h
    (Formalism.L2.SG.Pf.ZsVolFin.orbitFinite_holds M δ u u' F0 what₂)

end Formalism.L2.SG.Pf.ZsVolOrb

end
