import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SpanInst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.JInjRdOf
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormFrameReadingsLinearIndependentStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HolomorphicCuspFormsFramesLeSpanShortThetaReadinStatement

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.Dict

set_option synthInstance.maxHeartbeats 400000 in

theorem spanAt_record : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), LawsSh T → GamAt T.toCore → 0 < badN D → (∀ j, InR D j → ∀ k k', ((T.U j T.σ₀).X k).Gm = ((T.U j T.σ₀).X k').Gm ∧ ((T.U j T.σ₀).X k).ξ0 = ((T.U j T.σ₀).X k').ξ0) → ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka : WeightFamilies.Wt D j), LastPos (T.Q.Dw j) (wtA ka) → 8 * D.R.f * D.R.r + 4 ≤ ka.n → SpanAt ((recX h) j h1 h2) ka := by
  intro hC D T h hSh hG hb hU j h1 h2 ka hL hn
  have hj : InR D j := ⟨h1, h2⟩
  have hM : LawsM T.toCore := h.toLawsCore.toLawsM
  refine ReciprocityTheory.ChartRestriction.G.PullbackSections.spanAt_rec h j h1 h2 ka (GlobalTheory.T.cuspForm_frame_readings_linearIndependent D T hM j hj _ _) _
    (GlobalTheory.T.holomorphicCuspForms_frames_le_span_shortThetaReadings hC D T hM hSh hG hb hU j hj ka hn) ?_
  rintro _ ⟨x, hx, rfl⟩

  have hxC : x ∈ T.C j ka :=
    hSh.shCusp j hj (wtA ka) ka.n (dom_wtA ka) hL (dom_wtA ka) hL hx
  have hxR : x ∈ cutR T.C j ka := by
    show x ∈ T.C j ka ⊓ ⨅ (_ : ¬InR D j), ⊥
    exact Submodule.mem_inf.2 ⟨hxC, Submodule.mem_iInf _ |>.2 fun hn' => absurd hj hn'⟩
  apply Submodule.subset_span
  refine ⟨⟨x, hxR⟩, ?_, rfl⟩
  exact (Submodule.subset_span hx : x ∈ Submodule.span (𝓞 T.Q.c.F) (T.sh j ka))

end GlobalTheory.Dict
