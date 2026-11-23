import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassConstSucc
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsMassConstOne
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsFixF
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LiStatOf
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLand

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

theorem massConst_all (hH : HermRepUnram) (hLI : LIStat) {K F : Type} [Field K] [NumberField K]
    [StarRing K] [Field F] [NumberField F] [Algebra F K] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : IsFixF K F) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ m : ℕ, 1 ≤ m →
      MassConst K F m (c₁ * ∏ j ∈ Finset.Icc 2 m, Formalism.HermitianLatticesTheory.massRatioRightSide K j) := by
  obtain ⟨c₁, hc₁, h1⟩ := exists_massConst_one (K := K) (F := F) hK hF
  refine ⟨c₁, hc₁, fun m hm => ?_⟩
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · have he : Finset.Icc 2 (0 + 1) = ∅ := Finset.Icc_eq_empty (by norm_num)
      rw [he, Finset.prod_empty, mul_one]
      exact h1
    · have hc := ih hpos
      have hP : 0 < ∏ j ∈ Finset.Icc 2 m, Formalism.HermitianLatticesTheory.massRatioRightSide K j :=
        Finset.prod_pos fun j hj => massRatio_pos hK j (Finset.mem_Icc.mp hj).1
      have hstep := massConst_succ hH hLI hK hF (m := m + 1) (by omega) (mul_pos hc₁ hP)
        (by simpa using hc)
      rw [Finset.prod_Icc_succ_top (by omega), ← mul_assoc]
      exact hstep

theorem siegelMassRatio_of_LI (hH : HermRepUnram) (hLI : LIStat) : Formalism.HermitianLatticesTheory.SiegelMassRatio := by
  intro K _ _ _ hK M hM V V' _ _ _ _ _ _ _ _ h h' L L' hs hs' hL hL'
  obtain ⟨F, _, _, _, hF⟩ := exists_fixF K hK
  obtain ⟨c₁, hc₁, hall⟩ := massConst_all hH hLI hK hF
  have := finiteDimensional_of_ortho hL
  have := finiteDimensional_of_ortho hL'
  have e1 := hall M (by omega) V h L hs (isTotPosDef_of_ortho hK hs hL) (finrank_of_ortho hL)
    (isLattice_of_ortho hL) (isIntegralLat_of_ortho hL)
  have e2 := hall (M - 1) (by omega) V' h' L' hs' (isTotPosDef_of_ortho hK hs' hL')
    (finrank_of_ortho hL') (isLattice_of_ortho hL') (isIntegralLat_of_ortho hL')
  rw [lamG_eq_one_of_ortho hK hF hs hL, mul_one] at e1
  rw [lamG_eq_one_of_ortho hK hF hs' hL', mul_one] at e2
  have hprod : ∏ j ∈ Finset.Icc 2 M, Formalism.HermitianLatticesTheory.massRatioRightSide K j =
      (∏ j ∈ Finset.Icc 2 (M - 1), Formalism.HermitianLatticesTheory.massRatioRightSide K j) * Formalism.HermitianLatticesTheory.massRatioRightSide K M := by
    have := Finset.prod_Icc_succ_top (a := 2) (b := M - 1) (by omega)
      (fun j => Formalism.HermitianLatticesTheory.massRatioRightSide K j)
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ M)] at this
  have hP : 0 < ∏ j ∈ Finset.Icc 2 (M - 1), Formalism.HermitianLatticesTheory.massRatioRightSide K j :=
    Finset.prod_pos fun j hj => massRatio_pos hK j (Finset.mem_Icc.mp hj).1
  rw [e1, e2, hprod, div_eq_iff (by positivity)]
  ring

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem siegelMassRatio : Formalism.HermitianLatticesTheory.SiegelMassRatio := siegelMassRatio_of_LI hermRepUnram liStat

end Formalism.HermitianLattices.Ext.L3
