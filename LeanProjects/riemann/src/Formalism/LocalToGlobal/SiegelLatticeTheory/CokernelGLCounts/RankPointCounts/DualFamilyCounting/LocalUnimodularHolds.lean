import Formalism.SharpRestriction.CuspSpanNormBounds.LocSplitType
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomLocFOfVdZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsIsomScale

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open NumberField Formalism.HermitianLattices.Ext.L3

theorem local_unimodular_holds : Formalism.MainNotions.BridgeRowsGenus.LocUnimod := by
  intro F E _ _ _ _ _ _ hc S L M hL hM p hp huL huM
  have hF : IsFixF E F := fun a => by rw [hc.fixed a, RingHom.mem_range, Set.mem_range]
  obtain ⟨π, hπ, -, -⟩ := U0.exists_isUnif hF hp
  have hnd : G4.NondegOn S.hT ⊤ := by
    intro ξ _ hξ0
    by_contra hcon
    push Not at hcon
    exact hξ0 (S.nondeg.2 ξ fun w => hcon w Submodule.mem_top)
  obtain ⟨g, hg, -, hgM⟩ := G4.sd_main' (WA.isHermSemilocal_locRing hc.cmUnram hp) hπ S.herm
    two_ne_zero _ ⊤ ⊤ _ _ 1 le_rfl hnd (U0.isSD_loc hL hp.isPrime huL) (U0.isSD_loc hM hp.isPrime huM)
    (one_mem _) (fun _ => ⟨fun _ => Submodule.mem_top, fun _ => Submodule.mem_top⟩)
  exact ⟨g, hg, U0.gmap_eq_of_iff hgM⟩

end Formalism.L2.SG.Pf.Cnt
