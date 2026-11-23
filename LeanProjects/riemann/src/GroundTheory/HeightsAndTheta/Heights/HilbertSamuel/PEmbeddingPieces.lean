import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPiecesAdditive
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPieceDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingWeight
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

theorem EmbeddingPieces.proof (hA : PiecesAdditive.Statement) (hD : PieceDegree.Statement) :
    EmbeddingPieces.Statement := by
  intro K _ ι _ Ω _ F _ _ _ y D L c w hP hbir hL hex hw
  classical
  let S : (F →+* ℂ) → Set ((Σ k, ι k) → ℂ) := fun sg => {z | LiesOver y sg z}
  have hSc : ∀ sg, IsClosed (S sg) := fun sg => EmbeddingWeight.isClosed_liesOver y sg
  have hSs : ∀ sg (t : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, t k ≠ 0) → z ∈ S sg →
      (fun p => t p.1 * z p) ∈ S sg :=
    fun _ t _ _ hz => EmbeddingWeight.liesOver_smul hz t
  have hex' : ∀ z ∈ mcPts (mCoordIdeal y), ∃! sg, z ∈ S sg := hex
  have hind : ∀ (d : (F →+* ℂ) → ℝ), ∀ z ∈ mcPts (mCoordIdeal y), ∀ sg, LiesOver y sg z →
      ∑ s, d s * (S s).indicator (fun _ => (1 : ℝ)) z = d sg := by
    intro d z hz sg hsg
    rw [Finset.sum_eq_single sg]
    · rw [Set.indicator_of_mem (show z ∈ S sg from hsg), mul_one]
    · intro s _ hs
      have hns : z ∉ S s := fun h => hs ((hex z hz).unique h hsg)
      rw [Set.indicator_of_notMem hns, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ sg) h
  have hwL : ptsIntegral (mCoordIdeal y) (pot L) w = ptsIntegral (mCoordIdeal y) (pot L)
      (fun z => ∑ s, c s * (S s).indicator (fun _ => (1 : ℝ)) z) := by
    refine GroundTheory.Heights₂.Heights.Inter.DiagRAux.ptsIntegral_congr_mcPts _ (fun _ _ _ => rfl) ?_
    intro z hz
    obtain ⟨sg, hsg, -⟩ := hex z hz
    rw [hind c z hz sg hsg]
    exact (hw z hz sg hsg).self_of_nhds
  have h1 : ptsIntegral (mCoordIdeal y) (pot L) (fun _ => 1) = ptsIntegral (mCoordIdeal y) (pot L)
      (fun z => ∑ s, (fun _ => (1 : ℝ)) s * (S s).indicator (fun _ => (1 : ℝ)) z) := by
    refine GroundTheory.Heights₂.Heights.Inter.DiagRAux.ptsIntegral_congr_mcPts _ (fun _ _ _ => rfl) ?_
    intro z hz
    obtain ⟨sg, hsg, -⟩ := hex z hz
    rw [hind _ z hz sg hsg]
  rw [hwL, h1, hA K ι _ D L (F →+* ℂ) S c hP hL hSc hSs hex',
    hA K ι _ D L (F →+* ℂ) S (fun _ => 1) hP hL hSc hSs hex']
  rcases isEmpty_or_nonempty (F →+* ℂ) with he | ⟨⟨s0⟩⟩
  · simp [Finset.univ_eq_empty]
  · have hI : ∀ s, ptsIntegral (mCoordIdeal y) (pot L) ((S s).indicator fun _ => (1 : ℝ)) =
        ptsIntegral (mCoordIdeal y) (pot L) ((S s0).indicator fun _ => (1 : ℝ)) :=
      fun s => hD K ι Ω F y D L s s0 hP hbir hL hex
    simp only [hI, ← Finset.sum_mul, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard : (Fintype.card (F →+* ℂ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    field_simp

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
