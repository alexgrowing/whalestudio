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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SpanSteps
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.Shares

theorem spanMem_ssgt_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) {P : Frame X.Ψ r → ℂ} (hP : P ∈ X.SS la) : P ∈ X.SSgt la 0 := by
  refine ⟨hP, fun ξ hξ ν hν x hx => ?_⟩
  by_contra hne
  obtain ⟨⟨hsec, C, hC⟩, h0⟩ := hP
  have hpos := (moderateCoefficientPositivity_holds r X la P C 0 hsec (fun y hy => by simpa using hC y hy)).1 ξ hξ ν x hx hne
  have hsum : ∑ τ, ν τ = 0 := le_antisymm hν (Finset.sum_nonneg fun τ _ => hpos τ)
  have hz : ν = 0 := by
    funext τ
    exact (Finset.sum_eq_zero_iff_of_nonneg fun τ _ => hpos τ).1 hsum τ (Finset.mem_univ τ)
  subst hz
  exact hne (h0 ξ hξ x hx)

theorem spanMem_rdR {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (u : WeightFamilies.Wt D j)
    (F : (recB h.toLawsCore).Cusp j u) (k : (T.U j T.σ₀).Comp) :
    rdR h j F k ∈ ((T.U j T.σ₀).X k).SSgt (laR T j u k) 0 := by
  have hF : F.1 ∈ T.C j u := by
    rw [← cutR_eq T.C hj]; exact F.2
  exact spanMem_ssgt_zero _ _
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.readings_holomorphic_cuspForms (U := T.U j) siegelSpaceAlgebra_holds T.good_σ₀ (wtA u) u.n ⟨F.1, hF⟩ k)

theorem span_readings_components : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ u : WeightFamilies.Wt D j, (∀ g ∈ R.sp u Set.univ, ∃ f : ∀ k : (T.U j T.σ₀).Comp, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ, (∀ k, f k ∈ ((T.U j T.σ₀).X k).SSgt (laR T j u k) 0) ∧ ∀ y, g y = f (e y).1 (e y).2.1) ∧ (∀ (A : ∀ k : (T.U j T.σ₀).Comp, Set (Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ)) (s : Set ((recB h.toLawsCore).Cusp j u)), OntoBy h j u A s → ∀ f : ∀ k : (T.U j T.σ₀).Comp, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ, (∀ k, f k ∈ A k) → (fun y => f (e y).1 (e y).2.1) ∈ R.sp u s) ∧ ∀ (F : (recB h.toLawsCore).Cusp j u) (k : (T.U j T.σ₀).Comp), rdR h j F k ∈ ((T.U j T.σ₀).X k).SSgt (laR T j u k) 0 := by
  intro D T h j hj n R e hR u
  refine ⟨fun g hg => ?_, fun A s hA f hf => ?_, fun F k => spanMem_rdR h j hj u F k⟩
  · unfold Rdg.sp at hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨F, -, rfl⟩ := hg
      exact ⟨fun k => rdR h j F k, fun k => spanMem_rdR h j hj u F k, fun y => hR.2 u F y⟩
    | zero =>
      exact ⟨fun _ => 0, fun k => (siegelSpaceAlgebra_holds _ _ (laR T j u k) (laR T j u k) 0).2.2.1.1, fun _ => rfl⟩
    | add g g' _ _ hg hg' =>
      obtain ⟨f, hf, e1⟩ := hg
      obtain ⟨f', hf', e2⟩ := hg'
      refine ⟨fun k => f k + f' k,
        fun k => (siegelSpaceAlgebra_holds _ _ (laR T j u k) (laR T j u k) 0).2.2.1.2.1 _ (hf k) _ (hf' k), fun y => ?_⟩
      simp only [Pi.add_apply, e1, e2]
    | smul a g _ hg =>
      obtain ⟨f, hf, e1⟩ := hg
      refine ⟨fun k => a • f k,
        fun k => (siegelSpaceAlgebra_holds _ _ (laR T j u k) (laR T j u k) 0).2.2.1.2.2 a _ (hf k), fun y => ?_⟩
      simp only [Pi.smul_apply, e1]
  · obtain ⟨m, a, F, hF, hsum⟩ := hA f hf
    have : (fun y => f (e y).1 (e y).2.1) = ∑ i, a i • R.ev ((recPlusN h j hj n).inc u (F i)) := by
      funext y
      rw [hsum _ _ (e y).2.2, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, hR.2 u (F i) y, smul_eq_mul]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨F i, hF i, rfl⟩)

end GlobalTheory.Shares
