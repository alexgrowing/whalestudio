import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

noncomputable section
namespace GlobalTheory.FlatAnalytic

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem det_analyticAt {n : Type} [Fintype n] [DecidableEq n] {F : X → Matrix n n ℝ} {x : X}
    (hF : ∀ i j, AnalyticAt ℝ (fun y => F y i j) x) : AnalyticAt ℝ (fun y => (F y).det) x := by
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  fun_prop

theorem inv_analyticAt {n : Type} [Fintype n] [DecidableEq n] {F : X → Matrix n n ℝ} {x : X}
    (hF : ∀ i j, AnalyticAt ℝ (fun y => F y i j) x) (hd : (F x).det ≠ 0) (i j : n) :
    AnalyticAt ℝ (fun y => (F y)⁻¹ i j) x := by
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv',
    Matrix.adjugate_apply]
  have h1 : AnalyticAt ℝ (fun y => (F y).det⁻¹) x := (det_analyticAt hF).inv hd
  have h2 : AnalyticAt ℝ (fun y => ((F y).updateRow j (Pi.single i 1)).det) x := by
    refine det_analyticAt fun k l => ?_
    by_cases hk : k = j
    · subst hk; simp only [Matrix.updateRow_self]; exact analyticAt_const
    · simp only [Matrix.updateRow_ne hk]; exact hF k l
  exact h1.mul h2

end GlobalTheory.FlatAnalytic

namespace GlobalTheory.FlatAnalytic

theorem entry_analyticAt {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {g : ℕ} {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} (hτ : IsPeriodMap B τ)
    {b : E} (hb : b ∈ B) (i j : Fin g) : AnalyticAt ℝ (fun b => τ b i j) b :=
  (GlobalTheory.SCV.analyticOnNhd_of_differentiableOn hτ.1 (hτ.2.1 i j) b hb).restrictScalars

theorem flat_analytic {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {g : ℕ} {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} (hτ : IsPeriodMap B τ) :
    AnalyticOnNhd ℝ (flat τ) (cov B g) ∧
      AnalyticOnNhd ℝ (fun Q : E × Fl g => per (τ Q.1) Q.2) (B ×ˢ Set.univ) := by
  constructor
  · intro P hP
    have hb : P.1 ∈ B := hP.1
    have hτe : ∀ i j, AnalyticAt ℝ (fun Q : Pt E g => τ Q.1 i j) P := fun i j =>
      (entry_analyticAt hτ hb i j).comp analyticAt_fst
    have hA : ∀ i j, AnalyticAt ℝ (fun Q : Pt E g => (τ Q.1).map Complex.im i j) P := fun i j =>
      (Complex.imCLM.analyticAt _).comp (hτe i j)
    have hR : ∀ i j, AnalyticAt ℝ (fun Q : Pt E g => (τ Q.1).map Complex.re i j) P := fun i j =>
      (Complex.reCLM.analyticAt _).comp (hτe i j)
    have hd : ((τ P.1).map Complex.im).det ≠ 0 := ((hτ.2.2 _ hb).2.det_pos).ne'
    have hI : ∀ i j, AnalyticAt ℝ (fun Q : Pt E g => ((τ Q.1).map Complex.im)⁻¹ i j) P :=
      inv_analyticAt hA hd
    have hzi : ∀ j, AnalyticAt ℝ (fun Q : Pt E g => (Q.2 j).im) P := fun j =>
      ((Complex.imCLM.comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin g => ℂ) j).comp
        (ContinuousLinearMap.snd ℝ E (Fin g → ℂ)))).analyticAt P)
    have hzr : ∀ j, AnalyticAt ℝ (fun Q : Pt E g => (Q.2 j).re) P := fun j =>
      ((Complex.reCLM.comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin g => ℂ) j).comp
        (ContinuousLinearMap.snd ℝ E (Fin g → ℂ)))).analyticAt P)
    refine analyticAt_pi_iff.2 fun k => ?_
    rcases k with i | i
    · simp only [flat, flatOf, Sum.elim_inl, Matrix.vecMul, dotProduct]
      fun_prop
    · simp only [flat, flatOf, Sum.elim_inr, Matrix.vecMul, dotProduct, Pi.sub_apply]
      fun_prop
  · intro Q hQ
    have hb : Q.1 ∈ B := hQ.1
    have hτe : ∀ i j, AnalyticAt ℝ (fun Q : E × Fl g => τ Q.1 i j) Q := fun i j =>
      (entry_analyticAt hτ hb i j).comp analyticAt_fst
    have hx : ∀ k, AnalyticAt ℝ (fun Q : E × Fl g => ((Q.2 k : ℝ) : ℂ)) Q := fun k =>
      ((Complex.ofRealCLM.comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin g ⊕ Fin g => ℝ) k).comp
        (ContinuousLinearMap.snd ℝ E (Fl g)))).analyticAt Q)
    refine analyticAt_pi_iff.2 fun i => ?_
    have ht : ∀ j, AnalyticAt ℝ (fun Q : E × Fl g => ((Q.2 (Sum.inl j) : ℝ) : ℂ) * τ Q.1 j i) Q :=
      fun j => (hx _).mul (hτe j i)
    simp only [per, Pi.add_apply, Matrix.vecMul, dotProduct]
    exact (Finset.analyticAt_fun_sum _ fun j _ => ht j).add (hx _)

end GlobalTheory.FlatAnalytic
