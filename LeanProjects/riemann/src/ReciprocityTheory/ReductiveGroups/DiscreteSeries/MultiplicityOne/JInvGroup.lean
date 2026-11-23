import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvGroupA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvGroupB

noncomputable section

open MeasureTheory Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem stInvGroup (h : UnitaryGroupStructuralFacts) : StInvGroup := by
  obtain ⟨hB2, -, -, -, hUWb, -⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hHU, hHI, -, hCG, hCN, hCW, -⟩ := hB2
  intro k r Wp _ _ _ D X _ _ γ hγ
  have hG := hCG k r
  have hEG : embWb k r γ ∈ GV k r := by
    have hmem : embWb k r γ ∈ UWb k r := by rw [(hUWb k r).1]; exact ⟨γ, hγ.1, rfl⟩
    exact hmem.1
  have hE := hG.unit _ hEG
  have hz := InvGrp.frame_conjugation_fixes_point hG hEG D.z D.T_pos hγ.2
  let gb : Mt k r → Mt k r := fun x i j => gbar k r γ (Matrix.of x) i j
  have hgb : Continuous gb := by
    simp only [gb, gbar]; fun_prop
  have hff : ∀ x, gb (gb x) = x := by
    intro x; funext i j
    change gbar k r γ (gbar k r γ (Matrix.of x)) i j = x i j
    rw [InvGrp.gbar_gbar hE]; rfl
  have hl : ∀ U : Set (Mat k r), (∀ a ∈ U, gbar k r γ a ∈ U) →
      ∀ a ∈ U, ∃ b ∈ U, ∀ x, lmulM a (gb x) = gb (lmulM b x) := by
    intro U hU a ha
    refine ⟨gbar k r γ a, hU a ha, fun x => ?_⟩
    funext i j
    change (a * gbar k r γ (Matrix.of x)) i j = gbar k r γ (gbar k r γ a * Matrix.of x) i j
    rw [InvGrp.gbar_mul hE, InvGrp.gbar_gbar hE]
  have hG1 : ∀ g ∈ GV k r, gbar k r γ g ∈ GV k r := InvGrp.gbar_mem_GV hG hEG
  have hN1 : ∀ m ∈ Nset k r, gbar k r γ m ∈ Nset k r := InvGrp.gbar_mem_N hG hEG
  have hW1 : ∀ h ∈ UWset k r D.z, gbar k r γ h ∈ UWset k r D.z := InvGrp.gbar_mem_UW hG hEG D.z hz
  have hmapG : D.μG.map gb = D.μG :=
    InvGrp.map_invol_eq hHU hG D.haarG gb hgb hff (fun x hx => hG1 _ hx) (hl _ hG1)
  refine ⟨hG1, hN1, hW1, InvGrp.gbar_mem_UU hG hEG D.z hz, ?_, ?_, ?_, ?_, ?_⟩
  · intro g _ g' _
    unfold th
    rw [InvGrp.gbar_mul hE, Matrix.mul_inv_rev]
  · intro g hg
    unfold th
    rw [InvGrp.gbar_inv hE _ (hG.unit _ (hG1 g hg)), InvGrp.gbar_gbar hE]
    exact Matrix.nonsing_inv_nonsing_inv g (hG.unit g hg)
  · have hth : (fun x : Mt k r => fun i j => th k r γ (Matrix.of x) i j) = invM ∘ gb := by
      funext x; rfl
    rw [hth, ← Measure.map_map InvGrp.measurable_invM hgb.measurable, hmapG, hHI k r (GV k r) D.μG hG D.haarG]
  · exact InvGrp.map_invol_eq hHU (hCN k r) D.haarN gb hgb hff (fun x hx => hN1 _ hx) (hl _ hN1)
  · exact InvGrp.map_invol_eq hHU (hCW k r D.z) D.haarW gb hgb hff (fun x hx => hW1 _ hx) (hl _ hW1)

end ReciprocityTheory.ChartRestriction.DS.Mult1
