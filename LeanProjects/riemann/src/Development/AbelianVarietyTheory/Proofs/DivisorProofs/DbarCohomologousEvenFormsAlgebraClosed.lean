import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlas
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.ChernCalc

theorem dbarCoh_algebra : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) , DbarCoh A 1 1 ∧ (∀ w : A.Pt → Ev n, A.IsForm (fld A w) → A.dbar (fld A w) = 0 → DbarCoh A w w) ∧ ∀ (c : ℂ) (w w' z z' : A.Pt → Ev n), DbarCoh A w w' → DbarCoh A z z' → DbarCoh A (c • w) (c • w') ∧ DbarCoh A (w + z) (w' + z') ∧ DbarCoh A (w * z) (w' * z') := by
  intro M _ n A
  obtain ⟨h1, hc, hl, -, -⟩ := GlobalTheory.formCalculus M n A
  have h0 : A.IsForm 0 := by simpa using (hc 0 1 1 h1 h1).2.2.1
  have d0 : A.dbar 0 = 0 := by simpa using (hc 0 1 1 h1 h1).2.2.2.2.2.2.2.2
  have e1 : fld A 1 = 1 := rfl
  have d1 : A.dbar 1 = 0 := by
    have h := (hl 1 1 h1 h1).2
    rw [e1, mul_one, mul_one, one_mul] at h
    simpa using h
  have diag : ∀ w : A.Pt → Ev n, A.IsForm (fld A w) → A.dbar (fld A w) = 0 → DbarCoh A w w :=
    fun w hw dw => ⟨hw, hw, dw, dw, 0, h0, by rw [d0, sub_self]⟩
  refine ⟨diag 1 h1 d1, diag, ?_⟩
  rintro c w w' z z' ⟨hw, hw', dw, dw', u, hu, eu⟩ ⟨hz, hz', dz, dz', v, hv, ev⟩
  have es (x : A.Pt → Ev n) : fld A (c • x) = c • fld A x := rfl
  have ea (x y : A.Pt → Ev n) : fld A (x + y) = fld A x + fld A y := rfl
  have em (x y : A.Pt → Ev n) : fld A (x * y) = fld A x * fld A y := rfl
  have ecomm (x y : A.Pt → Ev n) : fld A x * fld A y = fld A y * fld A x := by rw [← em, ← em, mul_comm]
  have hs (α : A.Fld) (h : A.IsForm α) := (hc c α α h h).2.2.1
  have ds (α : A.Fld) (h : A.IsForm α) := (hc c α α h h).2.2.2.2.2.2.2.2
  have ha (α β : A.Fld) (h : A.IsForm α) (h' : A.IsForm β) := (hc c α β h h').1
  have hm (α β : A.Fld) (h : A.IsForm α) (h' : A.IsForm β) := (hc c α β h h').2.1
  have da (α β : A.Fld) (h : A.IsForm α) (h' : A.IsForm β) := (hc c α β h h').2.2.2.2.2.2.1
  refine ⟨⟨hs _ hw, hs _ hw', ?_, ?_, c • u, hs _ hu, ?_⟩,
    ⟨ha _ _ hw hz, ha _ _ hw' hz', ?_, ?_, u + v, ha _ _ hu hv, ?_⟩,
    ⟨hm _ _ hw hz, hm _ _ hw' hz', ?_, ?_, fld A w * v + fld A z' * u, ha _ _ (hm _ _ hw hv) (hm _ _ hz' hu), ?_⟩⟩
  · rw [es, ds _ hw, dw, smul_zero]
  · rw [es, ds _ hw', dw', smul_zero]
  · rw [es, es, ds _ hu, ← eu, smul_sub]
  · rw [ea, da _ _ hw hz, dw, dz, add_zero]
  · rw [ea, da _ _ hw' hz', dw', dz', add_zero]
  · rw [ea, ea, da _ _ hu hv, ← eu, ← ev]
    abel
  · rw [em, (hl w _ hw hz).2, dw, dz, zero_mul, mul_zero, add_zero]
  · rw [em, (hl w' _ hw' hz').2, dw', dz', zero_mul, mul_zero, add_zero]
  · rw [em, em, da _ _ (hm _ _ hw hv) (hm _ _ hz' hu), (hl w _ hw hv).2, (hl z' _ hz' hu).2, dw, dz', ← eu, ← ev,
      zero_mul, zero_mul, zero_add, zero_add, mul_sub, mul_sub, ecomm z' w, ecomm z' w']
    abel

end GlobalTheory.ChernCalc
