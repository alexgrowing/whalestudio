import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.AddBlockEquivSymmChartRingMap
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ExistsChartFormsIffIsFormSystem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial
open scoped ContDiff

noncomputable section

namespace SectionNorm

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n}

theorem evalCone_liftOld (D : GroundTheory.Heights₂.Heights.AddBlockData P) (w : Cone D.extSizes ℂ)
    (f : MvPolynomial (Coord n) ℤ) : evalCone w (D.liftOld f) = evalCone (D.basePart₂ w) f := by
  simp only [evalCone, GroundTheory.Heights₂.Heights.AddBlockData.liftOld, eval₂_rename]
  rfl

theorem evalCone_newCoord_mul (D : GroundTheory.Heights₂.Heights.AddBlockData P) (w : Cone D.extSizes ℂ)
    (j : Fin (D.size + 1)) (f : MvPolynomial (Coord n) ℤ) :
    evalCone w (X (D.newCoord j) * D.liftOld f) = D.newPart w j * evalCone (D.basePart₂ w) f := by
  rw [← evalCone_liftOld]
  simp only [evalCone, eval₂_mul, eval₂_X]
  rfl

def lineB {D : AddBlockData P} (G : ChartForms D) (Γ : GenSystem P) (N : HermLine n)
    (hN : N.deg = D.deg) (H : HermLine D.dims) (hH : H.deg = AddBlockData.eNew)
    (hmet : ∀ w, BlockNonzero w → H.metric w = hPlus G Γ N w) : HermLine D.dims where
  deg := D.degB
  metric := hB G Γ N
  metric_pos w hw := by
    show 0 < hPlus G Γ N w / N.metric (AddBlockData.basePart₂ w)
    rw [← hmet w hw]
    exact div_pos (H.metric_pos w hw) (N.metric_pos _ fun k ↦ hw (some k))
  metric_smul c w hc hw := by
    have hw' : BlockNonzero (fun o i ↦ c o * w o i : Cone D.dims ℂ) := fun o h ↦
      hw o (funext fun i ↦ by simpa [hc o] using congrFun h i)
    show hPlus G Γ N (fun o i ↦ c o * w o i) / N.metric (AddBlockData.basePart₂ (fun o i ↦ c o * w o i)) =
      (∏ o, ‖c o‖ ^ D.degB o) * (hPlus G Γ N w / N.metric (AddBlockData.basePart₂ w))
    have hNs : N.metric (AddBlockData.basePart₂ (fun o i ↦ c o * w o i : Cone D.dims ℂ)) =
        (∏ k, ‖c (some k)‖ ^ N.deg k) * N.metric (AddBlockData.basePart₂ w) :=
      N.metric_smul (fun k ↦ c (some k)) (AddBlockData.basePart₂ w) (fun k ↦ hc _) (fun k ↦ hw _)
    have hNp : 0 < N.metric (AddBlockData.basePart₂ w) := N.metric_pos _ fun k ↦ hw (some k)
    have hp : 0 < ∏ k, ‖c (some k)‖ ^ D.deg k :=
      Finset.prod_pos fun k _ ↦ zpow_pos (norm_pos_iff.2 (hc _)) _
    rw [← hmet _ hw', ← hmet _ hw, H.metric_smul c w hc hw, hH, hNs, hN, Fintype.prod_option,
      Fintype.prod_option]
    simp only [AddBlockData.eNew, AddBlockData.degB, Option.elim, zpow_one, zpow_zero,
      Finset.prod_const_one, mul_one, zpow_neg, Finset.prod_inv_distrib]
    field_simp
  metric_smooth := by
    have hold : ContDiff ℝ ∞ (fun w : Cone D.dims ℂ ↦ (AddBlockData.basePart₂ w : Cone n ℂ)) :=
      contDiff_pi.2 fun k ↦ contDiff_pi.1 contDiff_id (some k)
    have h1 : ContDiffOn ℝ ∞ (fun w ↦ H.metric w / N.metric (AddBlockData.basePart₂ w))
        {w : Cone D.dims ℂ | BlockNonzero w} :=
      H.metric_smooth.div (N.metric_smooth.comp hold.contDiffOn fun w hw k ↦ hw (some k))
        fun w hw ↦ (N.metric_pos _ fun k ↦ hw (some k)).ne'
    refine h1.congr fun w hw ↦ ?_
    show hPlus G Γ N w / N.metric (AddBlockData.basePart₂ w) = _
    rw [hmet w hw]

theorem exists_lineB (hM : GroundTheory.Heights₂.Heights.ChartMetric.Statement) (D : AddBlockData P)
    (G : ChartForms D) (Γ : GenSystem P) (N : HermLine n) (hN : N.deg = D.deg) :
    ∃ B : HermLine D.dims, B.deg = D.degB ∧ B.metric = hB G Γ N := by
  obtain ⟨⟨H, hdeg, hmet, -⟩, -⟩ := hM ι n P (AddBlockData.toObjects D) N hN G.d G.g G.isFormSystem
    Γ.r Γ.f Γ.δ Γ.isHomogGenerators
  exact ⟨lineB G Γ N hN H hdeg hmet, rfl, rfl⟩

theorem kleimanNef_field_of_alt (h : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.SectionNorm.Statement) :
    GroundTheory.Heights₂.Heights.SectionNorm.Statement := by
  intro ι _ _ n P D N hN d g hg r G δ hG c j hnot w hw hz
  have hext : (AddBlockData.ofObjects D).ext = D.extIdeal := AddBlockEq.addBlockEquiv_extIdeal D
  have hpts : D.extPoints = conePoints (AddBlockData.ofObjects D).ext ℂ := AddBlockEq.extPoints_eq D
  have h1 := (h ι n P (AddBlockData.ofObjects D) (ChartForms.ofFormSystem hg)
    (GenSystem.ofIsHomogGenerators hG) N hN).2 c j (by rw [hext]; exact hnot) w
    (by rw [← hpts]; exact hw) hz
  rw [evalCone_newCoord_mul, evalCone_liftOld, norm_mul, div_div]
  exact h1

theorem finiteTwists_degree_form_of_first
    (hL : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n)
      (D : AddBlockData P) (G : ChartForms D) (Γ : GenSystem P) (N : HermLine n), N.deg = D.deg →
        ∃ B : HermLine D.dims, B.deg = D.degB ∧ B.metric = hB G Γ N)
    (h : GroundTheory.Heights₂.Heights.SectionNorm.Statement) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.SectionNorm.Statement := by
  intro ι _ _ n P D G Γ N hN
  refine ⟨hL ι n P D G Γ N hN, fun c j hnot w hw hz ↦ ?_⟩
  have hext : (AddBlockData.toObjects D).extIdeal = D.ext := AddBlockEq.addBlockEquiv_symm_extIdeal D
  have hpts : (AddBlockData.toObjects D).extPoints = conePoints D.ext ℂ :=
    AddBlockEq.addBlockEquiv_symm_conePoints D
  have h1 := h ι n P (AddBlockData.toObjects D) N hN G.d G.g G.isFormSystem Γ.r Γ.f Γ.δ
    Γ.isHomogGenerators c j (by rw [hext]; exact hnot) w (by rw [hpts]; exact hw) hz
  erw [evalCone_newCoord_mul, evalCone_liftOld] at h1
  rw [norm_mul, div_div] at h1
  exact h1

theorem equiv (hM : GroundTheory.Heights₂.Heights.ChartMetric.Statement) :
    GroundTheory.Heights₂.Heights.SectionNorm.Statement ↔
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.SectionNorm.Statement :=
  ⟨finiteTwists_degree_form_of_first fun _ _ _ _ _ D G Γ N hN ↦ exists_lineB hM D G Γ N hN, kleimanNef_field_of_alt⟩

end SectionNorm

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
