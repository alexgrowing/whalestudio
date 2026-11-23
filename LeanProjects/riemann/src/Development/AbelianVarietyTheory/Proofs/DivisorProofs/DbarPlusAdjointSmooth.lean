import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodQuadraticFormsSmooth
open Matrix Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Pullback
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DbarSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}

theorem contDiffOn_d01 {m : ℕ} {U : Set (Pt E g)} (hU : IsOpen U) {s : Pt E g → Ext m}
    (hs : ContDiffOn ℝ ∞ s U) (v : Pt E g) : ContDiffOn ℝ ∞ (fun Q => d01 s Q v) U := by
  have hf : ContDiffOn ℝ ∞ (fun Q => fderiv ℝ s Q) U := hs.fderiv_of_isOpen hU (by simp)
  unfold d01
  exact ((hf.clm_apply contDiffOn_const).add
    ((hf.clm_apply contDiffOn_const).const_smul Complex.I)).const_smul _

theorem contDiffOn_d10 {m : ℕ} {U : Set (Pt E g)} (hU : IsOpen U) {s : Pt E g → Ext m}
    (hs : ContDiffOn ℝ ∞ s U) (v : Pt E g) : ContDiffOn ℝ ∞ (fun Q => d10 s Q v) U := by
  have hf : ContDiffOn ℝ ∞ (fun Q => fderiv ℝ s Q) U := hs.fderiv_of_isOpen hU (by simp)
  unfold d10
  exact ((hf.clm_apply contDiffOn_const).sub
    ((hf.clm_apply contDiffOn_const).const_smul Complex.I)).const_smul _

theorem contDiffOn_d10_scalar {U : Set (Pt E g)} (hU : IsOpen U) {f : Pt E g → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) (v : Pt E g) : ContDiffOn ℝ ∞ (fun Q => d10 f Q v) U := by
  have hd : ContDiffOn ℝ ∞ (fun Q => fderiv ℝ f Q) U := hf.fderiv_of_isOpen hU (by simp)
  unfold d10
  exact ((hd.clm_apply contDiffOn_const).sub
    ((hd.clm_apply contDiffOn_const).const_smul Complex.I)).const_smul _

theorem contDiffOn_wedge {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {m : ℕ} (i : Fin m)
    {U : Set X} {F : X → Ext m} (hF : ContDiffOn ℝ ∞ F U) :
    ContDiffOn ℝ ∞ (fun x => wedge i (F x)) U := by
  rw [contDiffOn_pi]
  intro S
  by_cases hS : i ∈ S
  · simp only [wedge, hS, if_true]
    exact contDiffOn_const.mul (contDiffOn_pi.1 hF _)
  · simp only [wedge, hS, if_false]
    exact contDiffOn_const

theorem contDiffOn_contr {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {m : ℕ} (i : Fin m)
    {U : Set X} {F : X → Ext m} (hF : ContDiffOn ℝ ∞ F U) :
    ContDiffOn ℝ ∞ (fun x => contr i (F x)) U := by
  rw [contDiffOn_pi]
  intro S
  by_cases hS : i ∈ S
  · simp only [contr, hS, if_true]
    exact contDiffOn_const
  · simp only [contr, hS, if_false]
    exact contDiffOn_const.mul (contDiffOn_pi.1 hF _)

theorem dbar_add_adj_smooth : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {g n : ℕ} (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ)
    (s : Pt E g → Ext (n + n + g)), IsPeriodMap B τ → ContDiffOn ℝ ∞ h (cov B g) →
    (∀ P ∈ cov B g, 0 < h P) → ContDiffOn ℝ ∞ s (cov B g) →
    ContDiffOn ℝ ∞ (fun Q => dbarV s Q + dbarAdj τ h s Q) (cov B g) := by
  intro E _ _ _ g n B τ h s hτ hh hpos hs
  have hU : IsOpen (cov B g) := hτ.1.prod isOpen_univ
  have hlog : ContDiffOn ℝ ∞ (fun Q => (Real.log (h Q) : ℂ)) (cov B g) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (hh.log fun Q hQ => (hpos Q hQ).ne')
  have him : ∀ a c, ContDiffOn ℝ ∞ (fun Q : Pt E g => (2 * imPart τ Q.1 a c : ℂ)) (cov B g) :=
    fun a c => contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
      (Complex.imCLM.contDiff.comp_contDiffOn (GlobalTheory.ThetaMetSmooth.entry_smooth hτ a c)))
  refine ContDiffOn.add ?_ ?_
  · unfold dbarV
    exact ContDiffOn.sum fun a _ => contDiffOn_wedge _ (contDiffOn_d01 hU hs _)
  · unfold dbarAdj pointDifference
    refine ContDiffOn.neg (ContDiffOn.sum fun a _ => ContDiffOn.sum fun c _ => ?_)
    exact (him a c).smul (contDiffOn_contr _
      ((contDiffOn_d10 hU hs _).add ((contDiffOn_d10_scalar hU hlog _).smul hs)))

end GlobalTheory.DbarSmooth
