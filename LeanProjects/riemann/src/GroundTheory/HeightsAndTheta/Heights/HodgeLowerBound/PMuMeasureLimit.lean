import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuMeasureLimit
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuRegMass
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuRegTruncLimit
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuRegTail
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuHomTail
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuHomMeanMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem ptsIntegral_div_two {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    (P : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) :
    ptsIntegral (e := e) P φ (fun z => g z / 2) = ptsIntegral (e := e) P φ g / 2 := by
  classical
  let m : ℝ ≃+ ℝ :=
    { toFun := fun x => x / 2, invFun := fun x => 2 * x, left_inv := fun x => by ring,
      right_inv := fun x => by ring, map_add' := fun x y => add_div x y 2 }
  have hhalf : ∀ (s : Set (((k : K) → ι k) → ℂ)) (F : (((k : K) → ι k) → ℂ) → ℝ),
      ∑ᶠ w ∈ s, F w / 2 = (∑ᶠ w ∈ s, F w) / 2 := by
    intro s F
    show ∑ᶠ w, ∑ᶠ (_ : w ∈ s), m (F w) = m (∑ᶠ w, ∑ᶠ (_ : w ∈ s), F w)
    rw [m.map_finsum]
    congr 1
    funext w
    rw [m.map_finsum]
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    rw [← MeasureTheory.integral_div]
    congr 1
    funext y
    have hs : ∀ w, sheetDensity P hΨ.choose φ (fun z => g z / 2) y w =
        sheetDensity P hΨ.choose φ g y w / 2 := by
      intro w
      unfold sheetDensity
      split_ifs <;> ring
    simp only [hs]
    exact hhalf _ _
  · simp

theorem MuMeasureLimit.proof (hM : MuRegMass.Statement) (hT : MuRegTruncLimit.Statement)
    (hR : MuRegTail.Statement) (hH : MuHomTail.Statement) (hN : MuHomMeanMass.Statement) :
    MuMeasureLimit.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B _ _
  refine ⟨?_, ?_⟩
  · have hU : Tendsto (fun t => ptsIntegral (e := D.n) (mCoordIdeal D.y)
        (fun _ z => Real.log ((muReg X.H X.S B t).h z)) X.Cd.cuspWeight) (𝓝[>] 0)
        (𝓝 (ptsIntegral (e := D.n) (mCoordIdeal D.y) (fun _ => phMu X.H) X.Cd.cuspWeight)) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hδ : 0 < ε / 4 := by positivity
      obtain ⟨R, hR1, hR2⟩ := ((hR II Ψ K ι Ω E D O Lt X B (ε / 4) hδ).and
        (Metric.tendsto_nhds.1 (hH II Ψ K ι Ω E D O Lt X) (ε / 4) hδ)).exists
      filter_upwards [hR1, Metric.tendsto_nhds.1 (hT II Ψ K ι Ω E D O Lt X B R) (ε / 4) hδ] with t h1 h2
      rw [Real.dist_eq] at h2 hR2 ⊢
      rw [abs_le] at h1
      rw [abs_lt] at h2 hR2 ⊢
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, hR2.1, hR2.2]
    simp only [ptsIntegral_div_two]
    rw [← hN II Ψ K ι Ω E D O Lt X]
    exact hU.div_const 2
  · exact tendsto_const_nhds.congr' ((hM II Ψ K ι Ω E D O Lt X B).mono fun t ht => ht.symm)

end GroundTheory.Heights₂.Heights.LowerBoundFree
