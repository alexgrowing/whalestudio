import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HorizontalLiftSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionFormSmoothStatement

set_option autoImplicit false

noncomputable section

open Matrix Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Pullback
open scoped ContDiff

namespace GlobalTheory.TorsionForm.Pullback.PieceSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}

theorem wedge_contDiffOn {m : ℕ} (i : Fin m) {U : Set (Pt E g)} {F : Pt E g → Ext m}
    (hF : ContDiffOn ℝ ∞ F U) : ContDiffOn ℝ ∞ (fun Q => wedge i (F Q)) U := by
  refine contDiffOn_pi.2 fun S => ?_
  by_cases hS : i ∈ S
  · simp only [wedge, hS, if_true]
    exact contDiffOn_const.mul (contDiffOn_pi.1 hF (S.erase i))
  · simp only [wedge, hS, if_false]
    exact contDiffOn_const

theorem d10_contDiffOn {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    {U : Set (Pt E g)} (hU : IsOpen U) {f : Pt E g → W} (hf : ContDiffOn ℝ ∞ f U)
    {w : Pt E g → Pt E g} (hw : ContDiffOn ℝ ∞ w U) :
    ContDiffOn ℝ ∞ (fun Q => d10 f Q (w Q)) U := by
  have hd : ContDiffOn ℝ ∞ (fun Q => fderiv ℝ f Q) U := hf.fderiv_of_isOpen hU (by simp)
  unfold d10
  exact ((hd.clm_apply hw).sub ((hd.clm_apply (hw.const_smul Complex.I)).const_smul Complex.I)).const_smul _

theorem d01_contDiffOn {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    {U : Set (Pt E g)} (hU : IsOpen U) {f : Pt E g → W} (hf : ContDiffOn ℝ ∞ f U)
    {w : Pt E g → Pt E g} (hw : ContDiffOn ℝ ∞ w U) :
    ContDiffOn ℝ ∞ (fun Q => d01 f Q (w Q)) U := by
  have hd : ContDiffOn ℝ ∞ (fun Q => fderiv ℝ f Q) U := hf.fderiv_of_isOpen hU (by simp)
  unfold d01
  exact ((hd.clm_apply hw).add ((hd.clm_apply (hw.const_smul Complex.I)).const_smul Complex.I)).const_smul _

end GlobalTheory.TorsionForm.Pullback.PieceSmooth

namespace GlobalTheory.TorsionForm.Pullback.PieceSmooth

theorem nabPiece_contDiffOn : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g n : ℕ} (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (s : Pt E g → Ext (n + n + g)), IsPeriodMap B τ → ContDiffOn ℝ ∞ h (cov B g) → (∀ P ∈ cov B g, 0 < h P) → ContDiffOn ℝ ∞ s (cov B g) → ∀ (i : Fin n) (v : E), ContDiffOn ℝ ∞ (fun Q => nabPiece τ h s Q i v) (cov B g) := by
  intro E _ _ _ g n B τ h s hτ hh hpos hs i v
  have hU : IsOpen (cov B g) := hτ.1.prod isOpen_univ
  have hhor : ContDiffOn ℝ ∞ (fun Q : Pt E g => hor τ Q v) (cov B g) := GlobalTheory.T.horizontal_lift_smooth B τ hτ v
  have hcon : ContDiffOn ℝ ∞ (fun Q : Pt E g => connForm τ Q.1 v (s Q)) (cov B g) :=
    GlobalTheory.T.connection_form_smooth B τ s hτ hs v
  have hlog : ContDiffOn ℝ ∞ (fun Q => (Real.log (h Q) : ℂ)) (cov B g) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (hh.log fun P hP => (hpos P hP).ne')
  have hHol : ContDiffOn ℝ ∞ (fun Q => nabHol τ h s Q v) (cov B g) := by
    unfold nabHol pointDifference
    exact (d10_contDiffOn hU hs hhor).add ((d10_contDiffOn hU hlog hhor).smul hs)
  have hAnti : ContDiffOn ℝ ∞ (fun Q => nabAnti τ s Q v) (cov B g) := by
    unfold nabAnti
    exact (d01_contDiffOn hU hs hhor).add hcon
  unfold nabPiece
  exact (wedge_contDiffOn _ hHol).add (wedge_contDiffOn _ hAnti)

end GlobalTheory.TorsionForm.Pullback.PieceSmooth
