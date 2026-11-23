import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

namespace GlobalTheory.SmoothComp

theorem smooth_comp : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (f : M → ℝ) (s : Set ℝ) (G : ℝ → ℝ), Continuous f → A.SmoothOn Set.univ (fun y => (f y : ℂ)) →
    IsOpen s → (∀ y, f y ∈ s) → ContDiffOn ℝ (⊤ : ℕ∞) G s →
      Continuous (fun y => G (f y)) ∧ A.SmoothOn Set.univ (fun y => (G (f y) : ℂ)) ∧ A.IsForm (A.fn (fun y => G (f y))) := by
  intro M _ n A f s G hf hfs hs hfs' hG
  have hcont : Continuous (fun y => G (f y)) :=
    hG.continuousOn.comp_continuous hf hfs'
  have hsm : A.SmoothOn Set.univ (fun y => (G (f y) : ℂ)) := by
    intro i
    have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f ∘ (A.e i).symm) ((A.e i).target ∩ (A.e i).symm ⁻¹' Set.univ) := by
      have := (Complex.reCLM.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).comp_contDiffOn (hfs i)
      refine this.congr fun v _ => ?_
      simp
    have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (G ∘ (f ∘ (A.e i).symm)) ((A.e i).target ∩ (A.e i).symm ⁻¹' Set.univ) :=
      hG.comp h1 fun v _ => hfs' _
    have h3 := (Complex.ofRealCLM.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).comp_contDiffOn h2
    refine h3.congr fun v _ => ?_
    simp
  exact ⟨hcont, hsm, A.isForm_fn hsm⟩

end GlobalTheory.SmoothComp
