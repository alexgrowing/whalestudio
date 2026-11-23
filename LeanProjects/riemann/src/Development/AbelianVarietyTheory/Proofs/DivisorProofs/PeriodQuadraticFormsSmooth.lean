import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReQuad
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
open Matrix GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.ThetaMet
open scoped Real ContDiff

noncomputable section
namespace GlobalTheory.ThetaMetSmooth

theorem contDiffOn_det_real' {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {ι : Type} [Fintype ι]
    [DecidableEq ι] {M : X → Matrix ι ι ℝ} {s : Set X} (h : ∀ a b, ContDiffOn ℝ ∞ (fun x => M x a b) s) :
    ContDiffOn ℝ ∞ (fun x => (M x).det) s := by
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => h _ _)

theorem contDiffOn_inv_entry' {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {ι : Type} [Fintype ι]
    [DecidableEq ι] {M : X → Matrix ι ι ℝ} {s : Set X} (h : ∀ a b, ContDiffOn ℝ ∞ (fun x => M x a b) s)
    (hdet : ∀ x ∈ s, (M x).det ≠ 0) (k a : ι) :
    ContDiffOn ℝ ∞ (fun x => (M x)⁻¹ k a) s := by
  have hadj : ContDiffOn ℝ ∞ (fun x => (M x).adjugate k a) s := by
    simp only [Matrix.adjugate_apply]
    refine contDiffOn_det_real' fun i j => ?_
    by_cases hi : i = a
    · subst hi; simpa [Matrix.updateRow_apply] using contDiffOn_const
    · simpa [Matrix.updateRow_apply, hi] using h i j
  refine ((contDiffOn_det_real' h).inv hdet |>.mul hadj).congr fun x hx => ?_
  rw [Matrix.inv_def, Ring.inverse_eq_inv']
  simp [smul_eq_mul]

theorem analyticOnNhd_of_differentiableOn {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {f : E → ℂ} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) :
    AnalyticOnNhd ℂ f U := by
  intro z hz
  let e : E ≃L[ℂ] (Fin (Module.finrank ℂ E) → ℂ) :=
    (Module.finBasis ℂ E).equivFun.toContinuousLinearEquiv
  have hU' : IsOpen (e.symm ⁻¹' U) := hU.preimage e.symm.continuous
  have hd : DifferentiableOn ℂ (f ∘ e.symm) (e.symm ⁻¹' U) :=
    hf.comp e.symm.differentiableOn (fun _ h => h)
  have ha : AnalyticAt ℂ (f ∘ e.symm) (e z) :=
    ReciprocityTheory.AnForm.Osgood.osgood _ _ _ hU' hd (e z) (by simpa using hz)
  have : f = (f ∘ e.symm) ∘ e := by ext y; simp
  rw [this]
  exact ha.comp ((e : E →L[ℂ] (Fin (Module.finrank ℂ E) → ℂ)).analyticAt z)

variable {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

theorem entry_smooth {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} (hτ : IsPeriodMap B τ) (i j : Fin g) :
    ContDiffOn ℝ ∞ (fun P : Pt E g => τ P.1 i j) (cov B g) := by
  have h1 : ContDiffOn ℂ ∞ (fun b => τ b i j) B :=
    (analyticOnNhd_of_differentiableOn hτ.1 (hτ.2.1 i j)).contDiffOn hτ.1.uniqueDiffOn
  have h2 : ContDiffOn ℝ ∞ (fun b => τ b i j) B := h1.restrict_scalars ℝ
  exact h2.comp contDiff_fst.contDiffOn fun P hP => hP.1

theorem im_smooth {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} (hτ : IsPeriodMap B τ) (i j : Fin g) :
    ContDiffOn ℝ ∞ (fun P : Pt E g => (τ P.1).map Complex.im i j) (cov B g) :=
  Complex.imCLM.contDiff.comp_contDiffOn (entry_smooth hτ i j)

theorem re_smooth {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} (hτ : IsPeriodMap B τ) (i j : Fin g) :
    ContDiffOn ℝ ∞ (fun P : Pt E g => (τ P.1).map Complex.re i j) (cov B g) :=
  Complex.reCLM.contDiff.comp_contDiffOn (entry_smooth hτ i j)

theorem inv_smooth {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} (hτ : IsPeriodMap B τ) (i j : Fin g) :
    ContDiffOn ℝ ∞ (fun P : Pt E g => ((τ P.1).map Complex.im)⁻¹ i j) (cov B g) :=
  contDiffOn_inv_entry' (im_smooth hτ) (fun P hP => (hτ.2.2 _ hP.1).2.det_pos.ne') i j

theorem zim_smooth (i : Fin g) : ContDiff ℝ ∞ (fun P : Pt E g => (P.2 i).im) :=
  Complex.imCLM.contDiff.comp ((contDiff_apply ℝ ℂ i).comp contDiff_snd)

theorem zre_smooth (i : Fin g) : ContDiff ℝ ∞ (fun P : Pt E g => (P.2 i).re) :=
  Complex.reCLM.contDiff.comp ((contDiff_apply ℝ ℂ i).comp contDiff_snd)

theorem p_smooth {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} (hτ : IsPeriodMap B τ) (i : Fin g) :
    ContDiffOn ℝ ∞ (fun P : Pt E g => ((fun k => (P.2 k).im) ᵥ* ((τ P.1).map Complex.im)⁻¹) i) (cov B g) := by
  simp only [vecMul, dotProduct]
  exact ContDiffOn.sum fun k _ => (zim_smooth k).contDiffOn.mul (inv_smooth hτ k i)

theorem smooth_main {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} (hτ : IsPeriodMap B τ) :
    ContDiffOn ℝ ∞ (flat τ) (cov B g) ∧ ContDiffOn ℝ ∞ (quad τ) (cov B g) ∧
      ContDiffOn ℝ ∞ (reQuad τ) (cov B g) := by
  have hflat : ContDiffOn ℝ ∞ (flat τ) (cov B g) := by
    rw [contDiffOn_pi]
    rintro (i | i)
    · exact p_smooth hτ i
    · simp only [flat, flatOf, Sum.elim_inr, Pi.sub_apply]
      refine (zre_smooth i).contDiffOn.sub ?_
      conv => arg 3; ext P; rw [vecMul, dotProduct]
      exact ContDiffOn.sum fun k _ => (p_smooth hτ k).mul (re_smooth hτ k i)
  have hp : ∀ i, ContDiffOn ℝ ∞ (fun P : Pt E g => flat τ P (Sum.inl i)) (cov B g) := fun i =>
    (contDiffOn_pi.1 hflat) (Sum.inl i)
  refine ⟨hflat, ?_, ?_⟩
  · unfold quad
    simp only [dotProduct, mulVec]
    exact ContDiffOn.sum fun i _ => (zim_smooth i).contDiffOn.mul
      (ContDiffOn.sum fun j _ => (inv_smooth hτ i j).mul (zim_smooth j).contDiffOn)
  · unfold reQuad
    simp only [dotProduct, mulVec]
    exact ContDiffOn.sum fun i _ => (hp i).mul
      (ContDiffOn.sum fun j _ => (re_smooth hτ i j).mul (hp j))

end GlobalTheory.ThetaMetSmooth
