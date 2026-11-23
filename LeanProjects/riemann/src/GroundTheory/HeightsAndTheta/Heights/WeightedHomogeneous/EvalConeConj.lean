import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.AddBlockEquivSymmChartRingMap
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ExistsChartFormsIffIsFormSystem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial _root_.GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.AddBlockData

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

omit [Fintype ι] [DecidableEq ι] in

theorem evalCone_conj (z : Cone n ℂ) (f : MvPolynomial (Coord n) ℤ) :
    evalCone (fun k i ↦ starRingEnd ℂ (z k i)) f = starRingEnd ℂ (evalCone z f) := by
  simp only [evalCone]
  rw [MvPolynomial.eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _

theorem den_conj {P : ArithVariety n} {D : AddBlockData P} (G : ChartForms D) (Γ : GenSystem P)
    (z : Cone n ℂ) : den G Γ (fun k i ↦ starRingEnd ℂ (z k i)) = den G Γ z := by
  simp only [den, evalCone_conj, Complex.norm_conj]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [show (fun j ↦ starRingEnd ℂ (z k j)) = fun j ↦ starRingEnd ℂ (z k j) from rfl, vectorL2Norm_conj]

theorem hPlus_conj {P : ArithVariety n} {D : AddBlockData P} (G : ChartForms D) (Γ : GenSystem P)
    (N : HermLine n) (hN : N.ConjInvariant) (w : Cone D.dims ℂ) (hw : BlockNonzero w) :
    hPlus G Γ N (fun o i ↦ starRingEnd ℂ (w o i)) = hPlus G Γ N w := by
  have hz : BlockNonzero (basePart₂ w) := fun k ↦ hw (some k)
  show N.metric (fun k i ↦ starRingEnd ℂ (basePart₂ w k i)) *
      l2Norm (fun i ↦ starRingEnd ℂ (newPart w i)) *
      Real.sqrt ((∑ c, ‖evalCone (fun k i ↦ starRingEnd ℂ (basePart₂ w k i)) (chartMonomial c G.d)‖ ^ 2) /
        den G Γ (fun k i ↦ starRingEnd ℂ (basePart₂ w k i))) = hPlus G Γ N w
  rw [hN _ hz, vectorL2Norm_conj, den_conj]
  simp only [evalCone_conj, Complex.norm_conj]
  rfl

theorem ChartMetric.equiv :
    GroundTheory.Heights₂.Heights.ChartMetric.Statement ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.ChartMetric.Statement := by
  constructor
  · intro hA ι _ _ n P D G Γ N hN
    obtain ⟨⟨H, hdeg, hmet, -⟩, hpts⟩ :=
      hA ι n P (toObjects D) N hN G.d G.g G.isFormSystem Γ.r Γ.f Γ.δ Γ.isHomogGenerators
    have hmet' : ∀ w : Cone D.dims ℂ, BlockNonzero w → H.metric w = hPlus G Γ N w := hmet
    refine ⟨⟨⟨H.deg, hPlus G Γ N, ?_, ?_, ?_⟩, hdeg, rfl⟩, ?_⟩
    · intro w hw
      rw [← hmet' w hw]
      exact H.metric_pos w hw
    · intro c w hc hw
      have hw' : BlockNonzero (fun k i ↦ c k * w k i) := by
        intro k hk
        apply hw k
        funext i
        have := congrFun hk i
        simpa [hc k] using this
      rw [← hmet' _ hw', ← hmet' _ hw]
      exact H.metric_smul c w hc hw
    · exact H.metric_smooth.congr fun w hw ↦ (hmet' w hw).symm
    intro w hw la c hc hj
    have hw' : w ∈ (toObjects D).extPoints := by
      have e : (toObjects D).extPoints = conePoints D.ext ℂ := AddBlockEq.addBlockEquiv_symm_conePoints D
      rw [e]
      exact hw
    exact hpts w hw' c la hc hj
  · intro hB ι _ _ n P D N hN d g hg r f δ hf
    obtain ⟨⟨A, hdeg, hmet⟩, hpts⟩ :=
      hB ι n P (ofObjects D) (ChartForms.ofFormSystem hg) (GenSystem.ofIsHomogGenerators hf) N hN
    refine ⟨⟨A, hdeg, fun w _ ↦ congrFun hmet w, fun hN' w hw ↦ ?_⟩, ?_⟩
    · exact (congrFun hmet _).trans ((hPlus_conj (ChartForms.ofFormSystem hg) (GenSystem.ofIsHomogGenerators hf) N hN' w hw).trans (congrFun hmet w).symm)
    · intro w hw c la hc hj
      have hw' : w ∈ conePoints (ofObjects D).ext ℂ := by
        have e : D.extPoints = conePoints (AddBlockEq.toIndefiniteRowSideFullHecke D).ext ℂ := AddBlockEq.extPoints_eq D
        rw [e] at hw
        exact hw
      exact hpts w hw' la c hc hj

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
