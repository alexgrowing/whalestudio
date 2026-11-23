import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.AxHSupA
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.PointwiseNormSectionEqFlagDomainNorm
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.PointwiseNormBddAboveISupEqCuspFormSupNorm
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory.FrameNorm.RecSup

theorem supBdd_and_supR_eq_supN : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j), ∀ (fn : ∀ σ : T.Q.c.F →+* ℂ, FrPt (T.Q.Xo j) T.Q.c (CAt σ) → Ix (T.Q.Dw j) → ℝ), GlobalTheory.FrameNorm.FnPin (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) (xiR D) fn → FnNe (T.Q.Xo j) T.Q.c fn ∧ (∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w), SupBdd (T.Q.Xo j) T.Q.c fn (wtA w) w.n F.1 ∧ ∀ sg, supR (T.Q.Xo j) T.Q.c fn sg (wtA w) w.n F.1 = (recB h.toLawsCore).supN j w sg F) ∧ ∀ (i : ℕ) (η : (recB h.toLawsCore).Cusp j (wEt D j i)), SupRLeRec h j fn i η := by
  intro D T h j hj fn hfn
  have hx : 0 < xiR D := (GlobalTheory.PinNum.xiR_pos_le_one D T.Q h.pins.1).1
  have hU : ∀ σ, Formalism.L2.PjFree.GoodEmb T.Q.c σ →
      Formalism.L2.PjFree.IsUnf (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) := fun σ hσ =>
    (Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf j hj σ ((Formalism.L2.PjFree.goodEmb_iff σ).1 hσ))
  have hmain : ∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w),
      SupBdd (T.Q.Xo j) T.Q.c fn (wtA w) w.n F.1 ∧
        ∀ sg, supR (T.Q.Xo j) T.Q.c fn sg (wtA w) w.n F.1 = (recB h.toLawsCore).supN j w sg F := by
    intro w F
    have hF : F.1 ∈ Formalism.L2.PjFree.cusp (T.Q.Xo j) T.Q.c (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) (wtA w) w.n :=
      cutR_le T.C j w F.2
    obtain ⟨h1, h2⟩ := GlobalTheory.FrameNorm.SupNorm.supBdd_and_supR_eq _ _ _ _ _ _ _ _ hU _ fn hx hfn _ _ (dom_wtA w) _ hF
    refine ⟨h1, fun sg => (h2 sg).trans ?_⟩
    show _ = cutN T.C T.Ns j w sg F
    unfold cutN
    rw [if_pos hj]
    rfl
  exact ⟨(GlobalTheory.FrameNorm.Comparison₂.ptNorm_eq_pnorm _ _ _ _ _ _ _ _ hU _ fn hx hfn).1, hmain,
    fun i η sg => ((hmain _ η).2 sg).le⟩

end GlobalTheory.FrameNorm.RecSup
