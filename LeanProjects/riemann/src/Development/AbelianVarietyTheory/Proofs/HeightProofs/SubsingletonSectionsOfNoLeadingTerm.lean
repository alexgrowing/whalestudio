import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.InnerEuclideanEmbeddingEqAverage
import Formalism.LocalToGlobal.ProjectiveLattices.CurveAsm
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtPf
import Formalism.LocalToGlobal.ProjectiveLattices.TieInst
import Formalism.LocalToGlobal.ProjectiveLattices.CombAlgOfCombBound
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Formalism.LocalToGlobal.ProjectiveLattices.FullExists
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Formalism.LocalToGlobal.ProjectiveLattices.AxHLAM

set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.RunJoin.NoPoint

section Abstract

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem subsingleton_sections_of_no_leadingTerm (G : GlobalFamilyData X ka wL wF) (hd : G.del = 0) (la : HeightOneSpectrum (𝓞 B.KO))
    (hB : InBasis G la) : Subsingleton (SectionSheafQuotient X la G.w wF) := by
  haveI : IsEmpty (Fin G.del) := by rw [hd]; infer_instance
  have h := hB.2
  rw [Set.range_eq_empty, Submodule.span_empty] at h
  exact (Submodule.subsingleton_iff (Kp X la G.N)).1 (subsingleton_of_bot_eq_top h)

theorem heights_of_del_zero (G : GlobalFamilyData X ka wL wF) (Q : ∀ la, LocalPointData G la) (Gc PH Prw Pet : ℝ) (hd : G.del = 0)
    (hB : ∀ la, InBasis G la) (hC : ∀ la, (Q la).InCurve) : Heights Q Gc PH Prw Pet := by
  haveI : IsEmpty (Fin G.del) := by rw [hd]; infer_instance
  have hI : ∀ la, (Q la).Ila = 0 := fun la => by
    haveI := subsingleton_sections_of_no_leadingTerm G hd la (hB la)
    unfold LocalPointData.Ila
    exact Module.length_eq_zero
  have hN : ∀ la, (Q la).Net = 0 := fun la => by
    haveI := subsingleton_sections_of_no_leadingTerm G hd la (hB la)
    haveI : Subsingleton (OsK X la G.w) := (hC la).2.2.1.subsingleton
    haveI : IsEmpty (PtsG G la) := ⟨fun ζ => ζ.isMaximal.ne_top (Subsingleton.elim _ _)⟩
    unfold LocalPointData.Net
    exact finsum_of_isEmpty _
  have hd' : (G.del : ℝ) = 0 := by rw [hd]; exact Nat.cast_zero
  refine ⟨fun la => by simp [hI la], by simp [hI, summable_zero], by simp [hI, hd'],
    fun _ => ⟨by simp [hN, summable_zero], by simp [hN, hd']⟩⟩

theorem inBasis_xplus (G : GlobalFamilyData X ka wL wF) (E : PtExt X) (hM : IntAtExt X E) (la : HeightOneSpectrum (𝓞 B.KO))
    (h : InBasis G la) : InBasis (gd2Xplus G E hM) la := h

theorem heights_xplus_of_del_zero (G : GlobalFamilyData X ka wL wF) (E : PtExt X) (hM : IntAtExt X E)
    (Q : ∀ la, LocalPointData (gd2Xplus G E hM) la) (Gc PH Prw Pet : ℝ) (hd : G.del = 0)
    (hB : ∀ la, InBasis G la) (hC : ∀ la, (Q la).InCurve) : Heights Q Gc PH Prw Pet :=
  heights_of_del_zero (gd2Xplus G E hM) Q Gc PH Prw Pet hd (fun la => inBasis_xplus G E hM la (hB la)) hC

end Abstract

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem heights_no_point : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (S : Scal (recB h.toLawsCore)) (G : GlobalFamilyData (recPJ h j hj) ka wL wF) (Q : ∀ la, LocalPointData (gd2Xplus G (extAll h j hj) (intAtExt_extAll h j hj)) la) (Gc PH Prw Pet : ℝ), G.del = 0 → (∀ la, InBasis G la) → (∀ la, (Q la).InCurve) → Heights Q Gc PH Prw Pet :=
  fun _ _ h j hj _ _ _ _ _ _ _ _ _ _ _ _ _ G Q Gc PH Prw Pet hd hB hC =>
    heights_xplus_of_del_zero G (extAll h j hj) (intAtExt_extAll h j hj) Q Gc PH Prw Pet hd hB hC

end GlobalTheory.RunJoin.NoPoint
