import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeClass

theorem edgeUniq_of : CrystallineSemistableComparison.E.StCol → CrystallineSemistableComparison.E.StAdd → CrystallineSemistableComparison.E.StUniq → CrystallineSemistableComparison.E.EdgeUniq := by
  intro _ hadd huniq R _ C _ F T hG j x x' h h' hx hx'
  obtain ⟨z, hz, st, rfl⟩ := hx
  obtain ⟨z', hz', st', rfl⟩ := hx'
  refine ⟨⟨z + z', ?_, (hadd R C F T j z z' j 0 x x' st st').1, ?_⟩, ?_⟩
  · rw [map_add, hz, hz', add_zero]
  · rfl
  · intro hv
    have st2 : T.St (z - z') j 0 (x - x') := (hadd R C F T j z z' j 0 x x' st st').2
    have hB : z - z' ∈ (cx F).B j := by
      cases j with
      | zero => exact huniq R C F T hG 0 (z - z') 0 0 (x - x') st2 hv
      | succ s =>
        obtain ⟨b, hb, hbx⟩ := hv
        obtain ⟨a, hax, sta⟩ := st2
        refine huniq R C F T hG (s + 1) (z - z') s 1 _ sta ?_
        refine ⟨a - b, ?_, ?_⟩
        · rw [map_sub, hax, hbx, sub_self]
        · rw [map_sub, hb, sub_zero, pow_zero, one_smul]
    exact (Submodule.Quotient.eq _).2 hB

end GlobalTheory.CompanionTheory.EdgeClass
