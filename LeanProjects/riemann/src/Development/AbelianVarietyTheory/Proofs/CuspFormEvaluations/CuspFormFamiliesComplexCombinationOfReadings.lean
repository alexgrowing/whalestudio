import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.KerExistsStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HolomorphicCuspFormsFramesLeSpanShortThetaReadinStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.BddSecCuspCongr

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.Shares

theorem rdOnto_rec : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) , LawsSh T → GamAt T.toCore → 0 < badN D → (∀ j, InR D j → ∀ k k', ((T.U j T.σ₀).X k).Gm = ((T.U j T.σ₀).X k').Gm ∧ ((T.U j T.σ₀).X k).ξ0 = ((T.U j T.σ₀).X k').ξ0) → ∀ u : WeightFamilies.Wt D j, 8 * D.R.f * D.R.r + 4 ≤ u.n → LastPos (T.Q.Dw j) (wtA u) → RdOnto h j u := by
  intro hCI D T h j hj hSh hGam hbad hX u hu hLast f hf
  have hcu : ∀ g ∈ T.sh j u, ∃ F : (recB h.toLawsCore).Cusp j u, F.1 = g := by
    intro g hg
    refine ⟨⟨g, ?_⟩, rfl⟩
    have hC := hSh.shCusp j hj (wtA u) u.n (dom_wtA u) hLast (dom_wtA u) hLast hg
    unfold cutR
    exact Submodule.mem_inf.2 ⟨hC, (Submodule.mem_iInf _).2 fun hn => absurd hj hn⟩
  have hspan := GlobalTheory.T.holomorphicCuspForms_frames_le_span_shortThetaReadings hCI D T h.toLawsCore.toLawsM hSh hGam hbad hX j hj u hu
  classical
  let f0 := fun (k : (T.U j T.σ₀).Comp) (x : Frame ((T.U j T.σ₀).X k).Ψ D.R.r) =>
    if x ∈ ((T.U j T.σ₀).X k).dom then f k x else 0
  have hf0 : f0 ∈ GlobalTheory.Dict.holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA u) u.n) := by
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · apply Submodule.subset_span
      intro k
      refine (GlobalTheory.DomCongr.bddSec_cusp_congr _ _ _ _ (f k) (f0 k) ?_).2 (hf k)
      intro x hx
      simp [f0, hx]
    · intro k x hx
      simp [f0, hx]
  obtain ⟨m, a, g, hg⟩ := Submodule.mem_span_set'.1 (hspan hf0)
  have hpre : ∀ i, ∃ F : (recB h.toLawsCore).Cusp j u, rdU (T.U j T.σ₀) F.1 = (g i).1 := by
    intro i
    obtain ⟨p, hp, hpg⟩ := (g i).2
    obtain ⟨F, rfl⟩ := hcu p hp
    exact ⟨F, hpg⟩
  choose F hF using hpre
  refine ⟨m, a, F, fun _ => Set.mem_univ _, ?_⟩
  intro k x hx
  have hfx : f k x = f0 k x := by simp [f0, hx]
  rw [hfx, ← hg]
  simp only [rdR, hF, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

end GlobalTheory.Shares
