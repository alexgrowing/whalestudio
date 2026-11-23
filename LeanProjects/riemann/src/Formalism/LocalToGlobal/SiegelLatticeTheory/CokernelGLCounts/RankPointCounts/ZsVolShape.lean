import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsUpUniMul
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexBStable

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolShape

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal
  Formalism.L2.SG.Pf.ZsVolCut Formalism.L2.SG.Pf.ZsVolGrp Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)

theorem mem_stZSet_iff (hA : ∀ p, Agree δ M p) (Z L : MatR D) (a : GLR D) :
    a ∈ stZSet M δ u u' Z L ↔ ∃ a' : GLR D, (a : MatR D) = L⁻¹ * (a' : MatR D) * L ∧ IsLoUni (a' : MatR D) ∧
      ∃ b : MatR D, IsUpUni b ∧ (a' : MatR D) * ZhatOM Z * b = ZhatOM Z ∧
        Formalism.L2.SG.Pf.StabIntSh.EntryShape D (a' : MatR D) b := by
  have hL := Formalism.L2.SG.Pf.StabIntSh.locShapeL (D := D)
  have hG := Formalism.L2.SG.Pf.StabIntSh.locShapeG (D := D)
  have hLG := Formalism.L2.SG.Pf.StabIntSh.locGlob (D := D)
  have hNZ := Formalism.L2.SG.Pf.StabIntSh.shapeNZ (D := D)
  constructor
  · rintro ⟨a', ha, hlo, b, hb, hZ, hp⟩
    refine ⟨a', ha, hlo, b, hb, hZ, (Formalism.L2.SG.Pf.StabIntSh.glob_iff hLG hNZ _ _).1 fun p => ?_⟩
    obtain ⟨l, ρ, hl, hρ, hm⟩ := hp p
    obtain ⟨e1, e2⟩ := Formalism.L2.SG.Pf.StabShape.uniq δ M u u' (hA p) _ _ hlo hb l ρ hl.1 hρ.1 hm
    rw [e1] at hl
    rw [e2] at hρ
    exact (Formalism.L2.SG.Pf.StabIntSh.loc_iff hL hG (p := p) hA hlo hb).1 ⟨hl, hρ⟩
  · rintro ⟨a', ha, hlo, b, hb, hZ, he⟩
    refine ⟨a', ha, hlo, b, hb, hZ, fun p => ?_⟩
    have h := (Formalism.L2.SG.Pf.StabIntSh.loc_iff hL hG (p := p) hA hlo hb).2
      ((Formalism.L2.SG.Pf.StabIntSh.glob_iff hLG hNZ _ _).2 he p)
    exact ⟨_, _, h.1, h.2, Formalism.L2.SG.Pf.StabShape.move δ M u u' (hA p) _ _ hlo hb⟩

end Formalism.L2.SG.Pf.ZsVolShape

end
