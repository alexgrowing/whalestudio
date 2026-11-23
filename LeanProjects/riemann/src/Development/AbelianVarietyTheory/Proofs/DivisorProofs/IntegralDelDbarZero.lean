import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSmoothPartitionUnityHolAtlasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIntegralFinSumCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDelChartSupportedMulFormEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasDelFinsetSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDbarCutoffMulFormEqZeroLocalStokesStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

namespace GlobalTheory.CxFormStokesBoth

open Set

section
variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem eq_sum_fn_mul {N : ℕ} (χ : Fin N → M → ℝ) (hχ : ∀ y, ∑ j, χ j y = 1) (η : A.Fld) :
    η = ∑ j, A.fn (χ j) * η := by
  rw [← Finset.sum_mul]
  have : (∑ j, A.fn (χ j)) = 1 := by
    funext x
    simp only [Finset.sum_apply, HolAtlas.fn, Pi.one_apply]
    rw [← map_sum, ← Complex.ofReal_sum, hχ, Complex.ofReal_one, map_one]
  rw [this, one_mul]

theorem dbar_sum {N : ℕ} (α : Fin N → A.Fld) (hα : ∀ j, A.IsForm (α j)) :
    A.dbar (∑ j, α j) = ∑ j, A.dbar (α j) := by
  have C := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A
  have h0 : A.IsForm 0 := by simpa using (C.2.1 0 1 1 C.1 C.1).2.2.1
  have hd0 : A.dbar 0 = 0 := by
    have := (C.2.1 0 0 0 h0 h0).2.2.2.2.2.2.1
    rw [add_zero] at this
    exact left_eq_add.mp this
  have key : ∀ s : Finset (Fin N), A.IsForm (∑ j ∈ s, α j) ∧ A.dbar (∑ j ∈ s, α j) = ∑ j ∈ s, A.dbar (α j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using ⟨h0, hd0⟩
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have := C.2.1 0 (α a) _ (hα a) ih.1
      exact ⟨this.1, by rw [this.2.2.2.2.2.2.1, ih.2]⟩
  exact (key Finset.univ).2
end

theorem stokes : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n),
    ∀ η : A.Fld, A.IsForm η → A.integral (A.del η) = 0 ∧ A.integral (A.dbar η) = 0 := by
  intro M _ _ _ _ _ _ n A η hη
  have C := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A
  obtain ⟨N, c, χ, hs, hsupp, hone⟩ := GlobalTheory.T.exists_finite_smooth_partition_unity_holAtlas A
  have hf : ∀ j, A.IsForm (A.fn (χ j) * η) := fun j =>
    (C.2.1 0 _ _ (HolAtlas.isForm_fn A (hs j)) hη).2.1
  have hdec := eq_sum_fn_mul A χ hone η
  constructor
  · rw [hdec, GlobalTheory.T.holAtlas_del_finset_sum A _ hf, GlobalTheory.T.holAtlas_integral_fin_sum_compact A _ (fun j => (C.2.1 0 _ _ (hf j) (hf j)).2.2.2.1)]
    exact Finset.sum_eq_zero fun j _ => GlobalTheory.T.integral_del_chartSupported_mul_form_eq_zero A η (χ j) (c j) hη (hs j) (hsupp j)
  · rw [hdec, dbar_sum A _ hf, GlobalTheory.T.holAtlas_integral_fin_sum_compact A _ (fun j => (C.2.1 0 _ _ (hf j) (hf j)).2.2.2.2.1)]
    exact Finset.sum_eq_zero fun j _ => GlobalTheory.T.integral_dbar_cutoff_mul_form_eq_zero_local_stokes A η (χ j) (c j) hη (hs j) (hsupp j)

end GlobalTheory.CxFormStokesBoth
