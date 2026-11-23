import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwo.GoodAdd

variable {Φ : Type} [Fintype Φ]

open Classical in
theorem wirt_contDiffOn {U : Set (Φ → ℂ)} (hU : IsOpen U) {f : (Φ → ℂ) → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) (τ : Φ) (b : Bool) : ContDiffOn ℝ ∞ (wirt τ b f) U := by
  have hd : ContDiffOn ℝ ∞ (fun y => fderiv ℝ f y) U :=
    hf.fderiv_of_isOpen hU (by simp)
  have h1 : ContDiffOn ℝ ∞ (fun y => fderiv ℝ f y (Pi.single τ 1)) U :=
    hd.clm_apply contDiffOn_const
  have h2 : ContDiffOn ℝ ∞ (fun y => fderiv ℝ f y (Pi.single τ I)) U :=
    hd.clm_apply contDiffOn_const
  unfold wirt
  exact (h1.add (contDiffOn_const.mul h2)).div_const _

theorem wirtWord_contDiffOn {U : Set (Φ → ℂ)} (hU : IsOpen U) (w : List (Φ × Bool)) {f : (Φ → ℂ) → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) : ContDiffOn ℝ ∞ (wirtWord w f) U := by
  induction w with
  | nil => simpa [wirtWord_nil] using hf
  | cons a w ih => rw [wirtWord_cons]; exact wirt_contDiffOn hU ih _ _

theorem wirt_congr {U : Set (Φ → ℂ)} (hU : IsOpen U) {f g : (Φ → ℂ) → ℂ} (h : Set.EqOn f g U)
    (τ : Φ) (b : Bool) : Set.EqOn (wirt τ b f) (wirt τ b g) U := by
  intro z hz
  have he : f =ᶠ[nhds z] g := Filter.eventuallyEq_of_mem (hU.mem_nhds hz) h
  simp only [wirt, he.fderiv_eq]

theorem wirt_add {f g : (Φ → ℂ) → ℂ} {z : Φ → ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) (τ : Φ) (b : Bool) :
    wirt τ b (f + g) z = wirt τ b f z + wirt τ b g z := by
  have h : fderiv ℝ (f + g) z = fderiv ℝ f z + fderiv ℝ g z := fderiv_add hf hg
  simp only [wirt, h, ContinuousLinearMap.add_apply]
  ring

theorem wirtWord_add {U : Set (Φ → ℂ)} (hU : IsOpen U) (w : List (Φ × Bool)) {f g : (Φ → ℂ) → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) :
    Set.EqOn (wirtWord w (f + g)) (wirtWord w f + wirtWord w g) U := by
  induction w with
  | nil => intro z _; rfl
  | cons a w ih =>
    intro z hz
    rw [wirtWord_cons, wirtWord_cons, wirtWord_cons, wirt_congr hU ih _ _ hz]
    have hf' := wirtWord_contDiffOn hU w hf
    have hg' := wirtWord_contDiffOn hU w hg
    exact wirt_add ((hf'.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))
      ((hg'.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)) _ _

theorem upperHalf_isOpen (F : Type) [Field F] [NumberField F] : IsOpen (upperHalf F) := by
  have : upperHalf F = ⋂ τ : Emb F, {z : Emb F → ℂ | 0 < (z τ).im} := by
    ext z; simp [upperHalf]
  rw [this]
  exact isOpen_iInter_of_finite fun τ =>
    isOpen_lt continuous_const (Complex.continuous_im.comp (continuous_apply τ))

end GlobalTheory.HeckeTwo.GoodAdd

theorem GlobalTheory.HeckeTwo.isGood_add : ∀ (F : Type) [Field F] [NumberField F] (P Q : ℂ → (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) → ℂ), GlobalTheory.HeckeTwo.IsGood P → GlobalTheory.HeckeTwo.IsGood Q → GlobalTheory.HeckeTwo.IsGood (fun σ z => P σ z + Q σ z) := by
  intro F _ _ P Q hP hQ
  have hU := GlobalTheory.HeckeTwo.GoodAdd.upperHalf_isOpen F
  refine ⟨fun σ hσ => (hP.1 σ hσ).add (hQ.1 σ hσ), fun w z hz => ?_⟩
  refine ((hP.2 w z hz).add (hQ.2 w z hz)).congr fun σ hσ => ?_
  exact GlobalTheory.HeckeTwo.GoodAdd.wirtWord_add hU w (hP.1 σ hσ) (hQ.1 σ hσ) hz
