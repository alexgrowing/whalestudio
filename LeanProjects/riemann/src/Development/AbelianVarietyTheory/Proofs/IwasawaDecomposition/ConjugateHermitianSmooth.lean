import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
open AlgebraicGeometry CategoryTheory Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CxPts GlobalTheory.GradedNorm
open scoped ComplexOrder

namespace GlobalTheory

open scoped ContDiff

theorem AnRead.smoothOn_conjTranspose_mul_mul :
    ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D m : ℕ} (R : AnRead p σ D) (S : Set (CxPts p σ)), IsOpen S → ∀ (A M : CxPts p σ → Matrix (Fin m) (Fin m) ℂ), (∀ a b, R.HoloOn S (fun y => A y a b)) → (∀ a b, R.SmoothOn S (fun y => (M y a b).re) ∧ R.SmoothOn S (fun y => (M y a b).im)) → ∀ a b : Fin m, R.SmoothOn S (fun y => (((A y)ᴴ * M y * A y) a b).re) ∧ R.SmoothOn S (fun y => (((A y)ᴴ * M y * A y) a b).im) := by
  intro k _ Y p σ D m R S hS A M hA hM a b
  have hC : ∀ i, ContDiffOn ℝ ∞ ((fun y => ((A y)ᴴ * M y * A y) a b) ∘ (R.chart i).e.symm)
      ((R.chart i).e.target ∩ (R.chart i).e.symm ⁻¹' S) := by
    intro i
    set e := (R.chart i).e
    have hU := GlobalTheory.ChartGlue.isOpen_over e hS
    have hAe : ∀ c d, ContDiffOn ℝ ∞ (fun v => A (e.symm v) c d) (e.target ∩ e.symm ⁻¹' S) :=
      fun c d => GlobalTheory.ChartGlue.contDiffOn_real hU (hA c d i)
    have hAc : ∀ c d, ContDiffOn ℝ ∞ (fun v => star (A (e.symm v) c d)) (e.target ∩ e.symm ⁻¹' S) :=
      fun c d => Complex.conjCLE.contDiff.comp_contDiffOn (hAe c d)
    have hMe : ∀ c d, ContDiffOn ℝ ∞ (fun v => M (e.symm v) c d) (e.target ∩ e.symm ⁻¹' S) := by
      intro c d
      have h1 : ContDiffOn ℝ ∞ (fun v => (M (e.symm v) c d).re) (e.target ∩ e.symm ⁻¹' S) := (hM c d).1 i
      have h2 : ContDiffOn ℝ ∞ (fun v => (M (e.symm v) c d).im) (e.target ∩ e.symm ⁻¹' S) := (hM c d).2 i
      have hf : (fun v => M (e.symm v) c d) = fun v => (((M (e.symm v) c d).re : ℝ) : ℂ) +
          (((M (e.symm v) c d).im : ℝ) : ℂ) * Complex.I := by
        funext v; exact (Complex.re_add_im _).symm
      rw [hf]
      exact (Complex.ofRealCLM.contDiff.comp_contDiffOn h1).add
        ((Complex.ofRealCLM.contDiff.comp_contDiffOn h2).mul contDiffOn_const)
    show ContDiffOn ℝ ∞ (fun v => ((A (e.symm v))ᴴ * M (e.symm v) * A (e.symm v)) a b) _
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact ContDiffOn.sum fun x _ => (ContDiffOn.sum fun c _ => (hAc c a).mul (hMe c x)).mul (hAe x b)
  exact ⟨fun i => Complex.reCLM.contDiff.comp_contDiffOn (hC i),
    fun i => Complex.imCLM.contDiff.comp_contDiffOn (hC i)⟩

end GlobalTheory
