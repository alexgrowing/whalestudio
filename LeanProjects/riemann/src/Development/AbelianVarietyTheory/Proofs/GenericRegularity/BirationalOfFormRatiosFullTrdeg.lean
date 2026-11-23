import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IsAlgebraicOfTrdegEq
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FinrankHostDivTwo
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExtendByZeroConstMul

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.Reg

theorem birSt_of_ratios_trdeg :
    ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c), ∀ (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF), ((∀ Z : Comp (T.Q.Xo j) T.Q.c, ∃ k₀, evC hG Z ((G.w k₀ : (recB h.toLawsCore).Cusp j wL) : T.R j) ≠ 0 ∧ Algebra.trdeg T.Q.c.F (IntermediateField.adjoin T.Q.c.F (Set.range fun k => evC hG Z ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j) / evC hG Z ((G.w k₀ : (recB h.toLawsCore).Cusp j wL) : T.R j))) = WeightFamilies.dimY D j) → BIRSt h j hj hG G) ∧ (BigAt h j hj hG G → BIRSt h j hj hG G) := by
  intro D T h j hj hG ka wL wF G
  have htr := (GlobalTheory.FlagDim.fnFG_fnTrdeg_record D T.Q h.pins.2.2.2 j hj).2
  have hint := GlobalTheory.Reg.intFormSt_holds D T h j hj hG wL _ G.w
  exact ⟨fun hB => birSt_of h j hj hG htr G hB hint,
    fun hBig => birSt_of_big h j hj hG htr G hBig hint⟩

end GlobalTheory.Reg
