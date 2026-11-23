import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.BesselMultiplicityOneL2
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StSchurW
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.SepMinors

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 TopH

theorem theoremM_of (hIn : UnitaryGroupStructuralFacts) (hXi : XiExists)
    (hH : StBeHerm) (hP : StBePos) (hW : StSchurW) (hS : StSInt)
    (h0 : StSchurG) (h1 : StPairs) (h1' : StBeConv) (hD1 : StBeEquiv) (h2 : StRepro) (h3 : StSmooth)
    (hF : StFrame) (h4a : StInvGroup) (h4b : StInvChar) (h4c : StInvCC) (h5 : StReps) (h6 : StTransM)
    (h7 : StSym) (h7' : StSymBeta) (h8 : StBetaInf) (h9g : StDichoG) (h9w : StDichoW) (h10 : StMixed)
    (hR : RankOneMinors) : ThmM := by
  intro k r Wp _ _ _ D X hD hX ha
  have hGN : GNIntSharp := hIn.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ha0 : 0 ≤ X.a := le_trans (by unfold aM nR; positivity) ha
  obtain ⟨d, hd⟩ := h0 k r Wp D X hD hX
  have hInt := beInt_integrable_of D X hD hX ha h0 h1 h1'
  have hHV : ∀ u ∈ Vfl X, ∀ u' ∈ Vfl X, ∀ η ξ : Wp, ⟪ξ, beOp D X u u' η⟫_ℂ = ⟪beOp D X u' u ξ, η⟫_ℂ :=
    fun u hu u' hu' η ξ => hH k r Wp D X hD hX u hu u' hu' η ξ
  have hb0 : 0 ≤ X.a - AG k r - 1 := le_trans (by unfold AB; positivity) (half_ratio_le_segment_base_of_std D.k_pos ha)
  have hab : AB k r ≤ X.a - (X.a - AG k r - 1) := by
    have := AG_ge (r := r) D.k_pos; linarith
  have hbe : ∀ v ∈ Vfl X, ∃ C : ℝ, ∀ y ∈ GV k r,
      ‖beOp D X (X.σ y X.w) v‖ ≤ C * gN y ^ (X.a - AG k r - 1) := by
    intro v hv
    obtain ⟨Cp, hCp⟩ := h1 k r Wp D X hD hX d hd X.a X.a X.w (w_mem X) v hv
    rw [min_self] at hCp
    exact be_bound D X hb0 hCp (hS k r Wp D hD _ (half_ratio_le_segment_base_of_std D.k_pos ha))
  have hRep : ∀ u ∈ Vfl X, ∀ v ∈ Vfl X, beOp D X u v = (d : ℂ) • ∫ y : Mt k r,
      ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ • beOp D X (X.σ (Matrix.of y) X.w) v ∂D.μG :=
    fun u hu v hv => (h2 k r Wp D X hD hX ha d hd u hu v hv).1
  have hM : MinorsOn D X := minorsOn_of_DD D X hGN ha0 hd.1 hb0 hab hbe hRep hHV
    (minors_DD hIn hXi h3 (stCut0 hIn) (stCut1p hIn) (stCut2 hIn) (stCut3 hIn) (stCut4 hIn) h8 h7' h4c h4a
      hD1 h0 h1 h1' hW hF h9g h9w h10 D X hD hX ha)
  exact multOne_of_minors D X hHV (fun u hu ξ => hP k r Wp D X hD hX ha u hu ξ) hInt
    (fun u hu u' hu' h hh m hm => (hD1 k r Wp D X hD hX u u' (hInt u hu u' hu') h hh m hm).1) hM

end ReciprocityTheory.ChartRestriction.DS.Mult1
