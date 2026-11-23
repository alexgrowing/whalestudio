import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDelFnMulEqZeroOfIsForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormDelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormMul

set_option autoImplicit false

open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder

namespace GlobalTheory.CxForm.LocStokes

theorem integral_del_fn_mul_eq_zero : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (γ : A.Fld) (χ : M → ℝ) (i : A.ι), A.IsForm γ → A.SmoothOn univ (fun y => (χ y : ℂ)) → tsupport χ ⊆ (A.e i).source → A.integral (A.del (A.fn χ * γ)) = 0 := by
  intro M _ _ _ _ _ _ n A γ χ i hγ hχ hs
  exact integral_del_fn_mul_eq_zero_of_isForm A γ χ i hγ hχ hs
    (GlobalTheory.T.holAtlas_isForm_del A _ (FormMul.isForm_mul A _ _ (A.isForm_fn hχ) hγ))

end GlobalTheory.CxForm.LocStokes
